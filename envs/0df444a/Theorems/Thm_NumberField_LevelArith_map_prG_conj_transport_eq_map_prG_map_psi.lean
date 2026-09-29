-- Prove2me | Theorems.Thm_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi
-- name    : NumberField.LevelArith.map_prG_conj_transport_eq_map_prG_map_psi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/15f9f0b7-de6a-5b99-bf4e-1fe479760e46
-- title:
--   Local w-components of σ-transported H² classes agree
-- statement:
--   Let $S$ be a finite set of rational primes and $L\le F$ intermediate fields of $\overline{\mathbb Q}/\mathbb Q$, each finite over $\mathbb Q$, with $F$ normal over $\mathbb Q$; write $K=\,$`levelField L F hLF` for $F$ regarded as an extension of $L$, and assume $K/L$ is Galois. The data are: $\sigma\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ restricting to an automorphism $\tau$ of $L$; a ring automorphism $e$ of $K$ agreeing with $\sigma$ on $K$; a group automorphism $c$ of $\mathrm{Gal}(K/L)$ with $c(g)(e\,y)=e(g\,y)$; a surjective self-map $\mathrm{pl}$ of the height-one spectrum of $\mathcal O_K$ with $v_{\mathrm{pl}\,w}(e\,y)=v_w(y)$, together with ring isomorphisms $T_w:K_w\xrightarrow{\sim}K_{\mathrm{pl}\,w}$ extending $e$ on $K$; an action of $\mathrm{Gal}(K/L)$ on $(\mathbb A_K)^\times$ by group automorphisms, and a morphism $\psi$ from the restriction along $c^{-1}$ of the representation $(\mathbb A_K)^\times$ to that representation itself whose $(\mathrm{pl}\,w)$-component is $T_w$ applied to the $w$-component (`finPart`); a monoid homomorphism $\iota:\mathrm{Gal}(K/L)\to \mathrm{Gal}(\overline{\mathbb Q}/L)/\mathrm{Gal}(\overline{\mathbb Q}/F)$ with $\iota(\mathrm{levelGal}(g))=\bar g$; a morphism $\varphi$ from the restriction along $\iota$ of the $\mathrm{Gal}(\overline{\mathbb Q}/F)$-invariants quotient representation of `sUnitsMaxRep S L` (the representation of $\mathrm{Gal}(\overline{\mathbb Q}/L)$ on the subgroup `sUnitsMaxStable S L` of $\overline{\mathbb Q}^\times$) to the $S$-unit representation of $K/L$ at the places of $L$ above $S$, preserving values in $\overline{\mathbb Q}^\times$; the morphism $j$ sending an $S$-unit to its principal idèle; and, for each $w$, the morphism $\mathrm{pr}_w$ of representations of the decomposition subgroup at $w$ given by the $w$-component of an idèle unit. Finally $f,f^\sigma$ are $2$-cocycles of the quotient-to-invariants representation such that, on values in $\overline{\mathbb Q}^\times$, $f^\sigma(\bar s,\bar t)=\sigma\cdot f(\overline{\sigma^{-1}s\sigma},\overline{\sigma^{-1}t\sigma})$ for all $s,t\in\mathrm{Gal}(\overline{\mathbb Q}/L)$. The conclusion is that for every height-one prime $w$ of $\mathcal O_K$, writing $\tilde x(g)$ for the image of the class of $g$ in $H^2$ under the map induced by $\iota$ and by $\varphi$ followed by $j$, one has $(\mathrm{pr}_w)_*\,\tilde x(f^\sigma)=(\mathrm{pr}_w)_*\,H^2(c^{-1},\psi)\,\tilde x(f)$, the outer maps being those induced on $H^2$ by the inclusion of the decomposition subgroup together with $\mathrm{pr}_w$.
--
--   This is the compatibility statement comparing, place by place, the local components of the idèle-class presentation of a $2$-cocycle for $\mathrm{Gal}(F/L)$ with those of the presentation transported along $\sigma$; the comparison is the naturality step needed to identify the two readings of a class in $H^2$ as idèle classes. It is used by [`NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv`](thm.html#NumberField.LevelArith.apply_eq_apply_of_isBrauerLocalInv_of_algEquiv), where local invariants of the transported class are evaluated, and it relies on the surjectivity of `levelGal` and the identification of its kernel with $\mathrm{Gal}(\overline{\mathbb Q}/F)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_LevelArith_map_prG_conj_transport_eq_map_prG_map_psi.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_IdeleLocalInvariant
import Definitions.Def_NumberField_BrauerLocalInvariantChar
import Definitions.Def_NumberField_BrauerLocalInvariantPresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory MonoidalCategory Module Limits groupCohomology ExtCitation NumberField.LevelArith
open scoped Classical NumberField.LevelArith TensorProduct Pointwise
open scoped NumberField NumberField.PlaceDecomp
open M4aHerbrand
open IsDedekindDomain

theorem NumberField.LevelArith.map_prG_conj_transport_eq_map_prG_map_psi
    (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F] [Normal ℚ ↥F] [IsGalois ↥L ↥(levelField L F hLF)]

    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (τ : ↥L ≃ₐ[ℚ] ↥L) (hστ : ∀ y : ↥L, σ (y : AlgebraicClosure ℚ) = ((τ y : ↥L) : AlgebraicClosure ℚ))
    (e : ↥(levelField L F hLF) ≃+* ↥(levelField L F hLF)) (he : ∀ y : ↥(levelField L F hLF), ((e y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = σ ((y : ↥(levelField L F hLF)) : AlgebraicClosure ℚ))
    (c : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) ≃* (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (hc : ∀ (g : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), c g (e y) = e (g y))

    (pl : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)) → HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (hpls : Function.Surjective pl)
    (hpl : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), (pl w).valuation ↥(levelField L F hLF) (e y) = w.valuation ↥(levelField L F hLF) y)
    (Tc : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)), w.adicCompletion ↥(levelField L F hLF) ≃+* (pl w).adicCompletion ↥(levelField L F hLF))
    (hTc : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (y : ↥(levelField L F hLF)), Tc w (y : w.adicCompletion ↥(levelField L F hLF)) = ((e y : ↥(levelField L F hLF)) : (pl w).adicCompletion ↥(levelField L F hLF)))
    [MulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ]
    (ψ : Rep.res c.symm.toMonoidHom (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hψ : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ),
      finPart (pl w) (Additive.toMul (ψ.hom (Additive.ofMul z))) = Units.map (Tc w : w.adicCompletion ↥(levelField L F hLF) →* (pl w).adicCompletion ↥(levelField L F hLF)) (finPart w z))

    (ι : (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) →* (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))
    (hι : ∀ g : ↥L.fixingSubgroup, ι (levelGal L F hLF g) = (g : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (φ : Rep.res ι ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)) ⟶ NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S))
    (hφval : ∀ x, ((NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) (φ.hom x) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)
        = ((sUnitsMaxRep.val S L (x.1 : sUnitsMaxRep S L) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))
    (j : NumberField.SUnits.sUnitsRep ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) ⟶ Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ)
    (hj : ∀ y, Additive.toMul (j.hom y) =
      Units.map (algebraMap ↥(levelField L F hLF) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) : ↥(levelField L F hLF) →* AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF)) (NumberField.SUnits.val ↥L ↥(levelField L F hLF) (placesOverPrimesFinset ↥L S) y))
    (prG : ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      Rep.res (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (Rep.ofMulDistribMulAction (↥(levelField L F hLF) ≃ₐ[↥L] ↥(levelField L F hLF)) (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ) ⟶
        Rep.ofMulDistribMulAction (↥(NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w)) (w.adicCompletion ↥(levelField L F hLF))ˣ)
    (hprG : ∀ (w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF))) (z : (AdeleRing (𝓞 ↥(levelField L F hLF)) ↥(levelField L F hLF))ˣ), (prG w).hom (Additive.ofMul z) = Additive.ofMul (finPart w z))

    (f fσ : cocycles₂ ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype)))
    (hffσ : ∀ s t s' t' : ↥L.fixingSubgroup, σ⁻¹ * (s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = s' → σ⁻¹ * (t : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) * σ = t' →
        sUnitsMaxRep.val S L ((fσ ((s : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)
          = σ • sUnitsMaxRep.val S L ((f ((s' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype)), (t' : (↥L.fixingSubgroup ⧸ F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : ((sUnitsMaxRep S L).quotientToInvariants (F.fixingSubgroup.comap L.fixingSubgroup.subtype))) : sUnitsMaxRep S L)) :
    ∀ w : HeightOneSpectrum (𝓞 ↥(levelField L F hLF)),
      (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ fσ))
        = (groupCohomology.map (NumberField.PlaceDecomp.decomp ↥L ↥(levelField L F hLF) w).subtype (prG w) 2).hom
            ((groupCohomology.map c.symm.toMonoidHom ψ 2).hom ((groupCohomology.map ι (φ ≫ j) 2) (H2π _ f))) := by sorry
