-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp
-- name    : ModularCurve.XHDRModelAtP.not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1cb387f8-0c9f-532b-8ac9-163bd8b9d744
-- title:
--   Non-supersingular points avoid crossings and lie over the smooth locus
-- statement:
--   Fix a prime $p$ and a nonzero natural number $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the Laurent series `jqModC ℚ` (the series $q^{-1}$ times the integral $j$-numerator) lies in the subfield `qExpFunctionFieldC ℚ ⊤` of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the integral form ratios at full level. Let $\mathfrak{X}$ be a term of the structure `XHDRModelAtP p M H hpM hj`, that is, a model of the modular curve at level `ΓM M H` over the ring `R p`, proper, flat, integral, normal, with a smooth model at level `ΓN p M H hpM`, together with a curve model over $\overline{\mathbb{Q}}$, its pinning and comparison data, and the further data recorded by that structure. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the predicate `LiesOverPrime p`), whose residue field $\kappa$ is algebraically closed of characteristic $p$, and let $\rho : \mathrm{R}\,p \to A$ be a ring homomorphism whose composition with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map of `R p`. Let $x$ be a point of the scheme underlying the curve model $\mathfrak{X}$`.Mfib A hA ρ hρ`, assumed closed, and assume that the place of the $q$-expansion function field `qExpFunctionFieldC κ (ΓN p M H hpM)` attached to $x$ by the bijection `placeOfPoint` of that curve model does not lie in `ssPlacesQExp κ (ΓN p M H hpM) p`, that is, does not satisfy the predicate `IsSSPlaceQExp`. The conclusion is twofold: the image of $x$ under $\mathfrak{X}$`.efib A hA ρ hρ` followed by $\mathfrak{X}$`.comp A hA ρ hρ 0` does not lie in the range of the base map of $\mathfrak{X}$`.comp A hA ρ hρ 1`; and the image of that point under the first projection of the pullback of the structure morphism `toBase p (ΓM M H) hj` along $\operatorname{Spec}$ of the composite of $\rho$ with the residue map of $A$ lies in the subset $\mathfrak{X}$`.smoothLocus`.
--
--   In the geometry of the Deligne–Rapoport model at a prime exactly dividing the level, the special fibre is a union of two components meeting at the supersingular points; this is the per-point statement that a closed point of the fibre model whose place is not supersingular lies on the first component only and maps into the smooth locus of the model. It is used in the reduction of differentials attached to cusp forms (regularity at the non-supersingular places of that component) and in the local analysis of the associated Néron object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.not_mem_range_comp_one_and_mem_smoothLocus_of_placeOfPoint_not_mem_ssPlacesQExp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (x : (𝔛.Mfib A hA ρ hρ).C) (hx : x ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hss : (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨x, hx⟩ ∉ ssPlacesQExp (IsLocalRing.ResidueField ↥A) (ΓN p M H hpM) p) :
    (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base x ∉ Set.range (𝔛.comp A hA ρ hρ 1).base ∧
    (pullback.fst (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base
        ((𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base x) ∈ 𝔛.smoothLocus := by sorry
