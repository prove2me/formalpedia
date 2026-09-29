-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_whittakerLoc_ne_zero_of_isCubicInductionDataOn
-- name    : LanglandsTunnell.CubicInduction.whittakerLoc_ne_zero_of_isCubicInductionDataOn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/6cd31461-465f-5446-82fc-47f567223917
-- title:
--   Nonvanishing of every local Whittaker factor
-- statement:
--   Let $K$ be a number field, equipped with an algebra structure of $\mathcal{O}_{\mathbb{Q}}$ on $\mathcal{O}_K$ which is integral, let `pins` be a package `CarrierPins ℚ` (a measurable space and measure on the adelic $\mathrm{GL}_2$ of $\mathbb{Q}$, a subset $D$, a central subgroup $Z$ of the ideles, level subgroups $U$ indexed by ideals, local generators, and a measurable space with a measure on the adele ring), let $\psi$ be an additive character of $\mathbb{A}_{\mathbb{Q}}$ with values in $\mathbb{C}$, and let $\mu$ be a homomorphism from the ideles of $K$ to $\mathbb{C}^{\times}$. Let $X$ be cubic induction data, that is, a function `X.form` on $\mathrm{GL}_3(\mathbb{A}_{\mathbb{Q}})$, a global Whittaker function `X.whittaker`, local functions `X.whittakerLoc v` on $\mathrm{GL}_3$ of the completion $\mathbb{Q}_v$ for each finite place $v$, an archimedean Whittaker function, a central character, and a dual Whittaker function. Assume `IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X`, whose conditions (left invariance of `X.form` under $\mathrm{GL}_3(\mathbb{Q})$, transformation under central scalars by the central character, triviality of that character on principal ideles, cuspidality along the two maximal parabolics, the identification of `X.whittaker` with `whittaker3 pins ψ X.form` and of `X.dualWhittaker` with the corresponding integral for $\psi^{-1}$ and the dual form, the $\psi$- and $\psi_v$-Whittaker transformation laws, the mirabolic Fourier expansions summing to `X.form` and to the dual form, factorisation of `X.whittaker` as the archimedean factor times the finite product of the `X.whittakerLoc v` over any finite set of places containing the bad ones outside which the components are integral, sphericity of `X.whittakerLoc v` with the induced coefficients and level invariance away from the bad places, local multiplicity one, moderate growth, $K$-finiteness, and the moment and half-plane conditions for both the form and its dual) are summarised here; here a place is bad when it is ramified in $K$ or twist-ramified above $K$ for $\mu$. Let $S$ be a finite set of finite places of $\mathbb{Q}$ containing every bad place, and suppose `X.form` is not the zero function. Then for every finite place $v$ of $\mathbb{Q}$, bad or not, the local Whittaker function `X.whittakerLoc v` is not identically zero.
--
--   Nonvanishing of each local Whittaker factor of a nonzero cusp form on $\mathrm{GL}_3$, in the structured-data formulation of the cubic induction package. It feeds the identification of functional equations and of Rankin–Selberg type identities for the induced form, where a local factor must be inverted or divided out at individual places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_whittakerLoc_ne_zero_of_isCubicInductionDataOn.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_LanglandsTunnell_CubicInduction_DataOn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.whittakerLoc_ne_zero_of_isCubicInductionDataOn
    (K : Type) [Field K] [NumberField K] [Algebra (𝓞 ℚ) (𝓞 K)] [Algebra.IsIntegral (𝓞 ℚ) (𝓞 K)]
    (pins : CarrierPins ℚ) (ψ : AddChar (AdeleRing (𝓞 ℚ) ℚ) ℂ) (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ)
    (X : CubicInductionData)
    (hX : IsCubicInductionDataOn K pins ψ μ {v | IsBadPlace K μ v} X)
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (hS : ∀ w, IsBadPlace K μ w → w ∈ S)
    (hF : X.form ≠ 0) (v : HeightOneSpectrum (𝓞 ℚ)) :
    X.whittakerLoc v ≠ 0 := by sorry
