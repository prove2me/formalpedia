-- Prove2me | Theorems.Thm_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
-- name    : NumberField.LevelArith.exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/0cc83999-91cb-5938-bbfa-876d0a6efb47
-- title:
--   Local coboundaries yield a coboundary in an adic completion
-- statement:
--   Let $S$ be a finite set of rational primes and $L \le F$ intermediate fields of $\overline{\mathbb Q}/\mathbb Q$, both finite over $\mathbb Q$, with $F/\mathbb Q$ normal; write $F_L$ for `levelField L F hLF`, namely $F$ with its scalars extended to $L$, assumed normal over $L$. Let $\Gamma_L$ be the fixing subgroup of $L$ and $\Gamma_F \cap \Gamma_L$ the fixing subgroup of $F$ intersected with it, and let $\iota : \mathrm{Gal}(F_L/L) \to \Gamma_L/(\Gamma_F\cap\Gamma_L)$ be a homomorphism with $\iota(\mathrm{levelGal}(g))$ the class of $g$ for every $g \in \Gamma_L$, where `levelGal` is restriction of automorphisms to $F_L$. Let $M$ be the $\mathbb Z[\Gamma_L]$-module `sUnitsMaxRep S L` of $S$-units of the maximal extension attached to $S$ and $L$, and let $\varphi$ be a morphism of representations from the $(\Gamma_F\cap\Gamma_L)$-invariants of $M$, viewed through $\iota$ as a representation of $\mathrm{Gal}(F_L/L)$, to the $\mathbb Z[\mathrm{Gal}(F_L/L)]$-module of $S$-units of $F_L$ at the places `placesOverPrimesFinset L S` of $L$ above $S$, such that $\varphi$ does not change the underlying element of $\overline{\mathbb Q}^\times$. Let $f$ be a $2$-cocycle of $\Gamma_L/(\Gamma_F\cap\Gamma_L)$ with values in those invariants. Assume that for every $q \in S$ and every $\sigma \in \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$, writing $\lambda_\sigma$ for the composite of `primeLocalToGlobal q` (restriction to $\overline{\mathbb Q}$ of automorphisms of a fixed algebraic closure of $\mathbb Q_q$) with conjugation by $\sigma$, there is a $1$-cochain $c$ on $\lambda_\sigma^{-1}(\Gamma_L)$ with values in $M$ which satisfies the predicate `IsLevelConstant₁` relative to $\lambda_\sigma$ restricted to that subgroup, and such that $f(\overline{\lambda_\sigma g},\overline{\lambda_\sigma h}) = \lambda_\sigma(g)\cdot c(h) - c(gh) + c(g)$ for all $g,h$ there. Then for every place $v$ in `placesOverPrimesFinset L S` there exist a number field $K''$ with $L$- and $F_L$-algebra structures forming a scalar tower, with $K''/L$ Galois, and a height-one prime $w''$ of $\mathcal O_{K''}$ lying under which over $\mathcal O_{F_L}$ is the chosen place `PlaceAbove.above L F_L v` above $v$, together with a function $y$ from the decomposition group $D$ of $w''$ in $\mathrm{Gal}(K''/L)$ to the additive group of units of the $w''$-adic completion of $K''$, such that for all $g,h \in D$ the image in that completion of the $S$-unit value of the transported cocycle `mapCocycles₂ ι φ f` at the pair of restrictions of $g$ and $h$ to $F_L$ equals $g\cdot y(h) - y(gh) + y(g)$.
--
--   This is the finite-place step in the local–global analysis of $H^2$ of $S$-units: from the hypothesis that the class becomes a coboundary on each decomposition group $\Gamma_L \cap \sigma\,\mathrm{Gal}(\overline{\mathbb Q}_q/\mathbb Q_q)\,\sigma^{-1}$ for $q \in S$, one obtains, at each place above $S$, a splitting of the finite-level cocycle inside the completion of a Galois layer. It feeds the vanishing statement [`groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax`](thm.html#groupCohomology.eq_zero_of_forall_continuousH2Map_primeLocal_archimedean_eq_zero_pPrimary_continuousH2Sr_sUnitsMax), where the semilocal description of $S$-idèle cohomology is assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology ExtCitation IsDedekindDomain NumberField NumberField.LevelArith
open scoped NumberField.LevelArith NumberField.PlaceDecomp

theorem NumberField.LevelArith.exists_layer_coboundary_adicCompletion_of_forall_conj_primeLocal_coboundary
    (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
    [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [Normal ↥L ↥(levelField L F hLF)]
    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →*
      (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hιg : ∀ g : ↥L.fixingSubgroup,
      ι (levelGal L F hLF g) = (g : ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶
      NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφval : ∀ x,
      ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) :
          ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (f : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hloc : ∀ (q : ↥S) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ∃ c : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))) →
          sUnitsMaxRep S L,
        IsLevelConstant₁
            ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).comp
              (L.fixingSubgroup.comap
                ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))).subtype)) c ∧
          ∀ g h : ↥(L.fixingSubgroup.comap ((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes)))),
            ((f (((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup g : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype),
                  ((((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                      L.fixingSubgroup h : ↥L.fixingSubgroup) :
                    ↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
                (sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) :
              sUnitsMaxRep S L) =
              (sUnitsMaxRep S L).ρ
                  (((MulAut.conj σ).toMonoidHom.comp (primeLocalToGlobal (q : Nat.Primes))).subgroupComap
                    L.fixingSubgroup g) (c h) - c (g * h) + c g)
    (v : {v // v ∈ placesOverPrimesFinset ↥L S}) :
    ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra ↥L K'')
      (_ : Algebra ↥(levelField L F hLF) K'')
      (_ : IsScalarTower ↥L ↥(levelField L F hLF) K'') (_ : IsGalois ↥L K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 ↥(levelField L F hLF)) w'' = PlaceAbove.above ↥L ↥(levelField L F hLF) v.1)
      (y : PlaceDecomp.decomp ↥L K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp ↥L K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap ↥(levelField L F hLF) K'').toMonoidHom
              (SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S)
                ((mapCocycles₂ ι φ f)
                  (AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (g : K'' ≃ₐ[↥L] K''),
                    AlgEquiv.restrictNormalHom ↥(levelField L F hLF) (h : K'' ≃ₐ[↥L] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp ↥L K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g := by sorry
