-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/5369d129-01e7-50d1-a6ec-883b34b07384
-- title:
--   Split torus open in the joint degeneracy kernel
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, such that $p \nmid N_0$, let $A$ be a valuation subring of an algebraic closure of $\mathbf Q$ with $p$ lying in the nonunits of $A$ (the hypothesis `A.LiesOverPrime p`), let $\Lambda$ be level data `LevelData N₀ p A` — a structure morphism $\sigma_A$ from $\operatorname{Spec} A$ to the base, a scheme $X$ with a morphism $f$ to the base, a relative group law $\Lambda.L$ on $f$, and identifications of $J^0(N_0)$ and of its residue-field analogue with points of $f$ over the generic and the residue point — satisfying `Λ.IsJacobian`, and let $O$ be an object of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with its smooth separated surjective group scheme $g$ carrying the group law $O.L$, its toric rank $O.toricRank$ and its torus morphism $O.torusFibre$. Write $c$ for the residue point of $A$ followed by $\Lambda.\sigma_A$, and let $d\kappa_i$ ($i \in \{0,1\}$) denote the restriction of the two degeneracy morphisms $O.\mathrm{degeneracyHom}\,i$ to the fibres over $c$, i.e. the morphism from the base change of $g$ along $c$ to the base change of $\Lambda.f$ along $c$ obtained by `fibreRestrictAlong`; these are homomorphisms for the base-changed group laws because the degeneracy morphisms respect multiplication. Let $\mathcal H$ be `kerPair` of the base-changed law $\Lambda.L$ along the pair $d\kappa$, namely the fibre product over the special fibre of $g$ of the two kernels $d\kappa_i^{-1}(e)$, with the induced group law $L_{\mathcal H} =$ `kerPairLaw`. The assertion is that there exists a morphism $\iota$ from `torusScheme (ResidueField ↥A) O.toricRank` (the spectrum of `torusCoord` of the residue field of $A$ in $O.toricRank$ variables, whose coordinate ring is an additive monoid algebra on $\mathrm{Fin}\,O.toricRank \to \mathbf Z$) to $\mathcal H$ such that: $\iota$ followed by the canonical morphism `kerPairι` from $\mathcal H$ into the special fibre equals the underlying morphism of $O.torusFibre$; $\iota$ is an open immersion; and for every $n \in \mathbf N$, $\iota$ followed by the $n$-fold multiplication endomorphism `schemeNsmul` of $L_{\mathcal H}$ coincides with $\operatorname{Spec}$ of the map-domain ring homomorphism induced by multiplication by $n$ on $\mathrm{Fin}\,O.toricRank \to \mathbf Z$, followed by $\iota$.
--
--   This identifies the split torus of rank $O.toricRank$ with an open subscheme of the joint kernel of the two degeneracy morphisms on the special fibre at $p$ of the Néron object of level $N_0p$, compatibly with multiplication by $n$; it is the multiplicative-part input to the analysis of the character group in Ribet's level-lowering argument. It is used in bounding the number of points of the relevant kernel by a power of the toric rank.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_isOpenImmersion_torus_kerPair_degeneracyHom.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open AlgebraicGeometry

theorem ModularCurve.JZeroNeronObjectAtP.exists_isOpenImmersion_torus_kerPair_degeneracyHom
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) :
    letI dκ := fun i : Fin 2 =>
      NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) Λ.f O.g (O.degeneracyHom i)
    letI LH := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw
      (O.L.baseChange (resPt A ≫ Λ.σA)) (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ
      (fun i => GoodReductionJacobian.RelativeGroupLaw.IsHom.fibreRestrictAlong (resPt A ≫ Λ.σA)
        (fun t x y => O.degeneracyHom_mul i t x y))
    ∃ ι : torusScheme (ResidueField ↥A) O.toricRank ⟶
        RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ,
      ι ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) dκ = O.torusFibre.1 ∧
      IsOpenImmersion ι ∧
      ∀ n : ℕ, ι ≫ LH.schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫ ι := by sorry
