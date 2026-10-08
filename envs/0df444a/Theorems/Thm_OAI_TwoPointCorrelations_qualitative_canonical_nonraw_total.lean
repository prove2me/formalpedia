-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_qualitative_canonical_nonraw_total
-- name    : OAI.TwoPointCorrelations.qualitative_canonical_nonraw_total
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:48.739114+00:00
-- url     : https://prove2.me/theorems/87a17060-ef00-4303-a82d-3f8c864d32d3
-- title:
--   Under three analytic inputs, the non-raw complex bins of nonpretentious functions are small on average
-- statement:
--   Assume `ModFiveThetaInput`, `PrimeReciprocalInput` and `MRTShortExponentialInput`. Let $F,G$ be multiplicative, bounded by $1$ on positive integers, at least one `UniformlyNonpretentious`; $h>0$; $E$ finite; $W\ge1$. Then there is $C>0$ such that for all sufficiently large $L$, with $J$ = `primeSupplyCount W L`, $P$ = `centeredPrimeBands E (L^{199/200}) W J`, $Q$ = `paddingPrimeSupply E L`: for every $R\subseteq$ `retainedPrimeDivisors Q`, with $\eta=e^{-J}$ and bins $=\{0,\dots,\lfloor100L/\eta\rfloor\}$ (`paddingBinIndices L η`), for all sufficiently large $X$, every family of eligibility relations confined to the padding bins (`actualPaddingBin η (log d) j q`) and every $v$ with $|v_j|\le1$,
--
--   $$\Big|\sum_{j\in\mathrm{bins}}v_j\,\texttt{nonrawComplexBin}\big(P,R,\mathrm{eligible}_j,F,G,h,Xe^{j\eta}\big)\Big|\le C\,L^{-3/40}\,\texttt{paddingTiltNormalizer}(Q)\prod_i\sum_{p\in P_i}\frac1p.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.qualitative_canonical_nonraw_total`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem qualitative_canonical_nonraw_total (hP : ModFiveThetaInput)
    (hM : PrimeReciprocalInput) (hMRT : MRTShortExponentialInput)
    {F G : ℕ → ℂ} (hFm : Multiplicative F) (hGm : Multiplicative G)
    (hF : OneBounded F) (hG : OneBounded G)
    (hnp : UniformlyNonpretentious F ∨ UniformlyNonpretentious G)
    (h : ℕ) (hh : 0 < h) (E : Finset ℕ) (W : ℝ) (hW : 1 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ L : ℝ in atTop,
      let J := primeSupplyCount W L
      let P := centeredPrimeBands E (L ^ (199 / 200 : ℝ)) W J
      let Q := paddingPrimeSupply E L
      ∀ R : Finset ℕ, R ⊆ retainedPrimeDivisors Q →
      let η := Real.exp (-(J : ℝ))
      let bins := paddingBinIndices L η
      ∀ᶠ X : ℝ in atTop, ∀ (eligible : ℤ → ℕ → ℕ → Prop) (v : ℤ → ℂ),
      (∀ j ∈ bins, ∀ d q, eligible j d q → actualPaddingBin η (Real.log d) j q) →
      (∀ j ∈ bins, ‖v j‖ ≤ 1) →
      ‖∑ j ∈ bins, v j * nonrawComplexBin P R (eligible j) F G h
        (X * Real.exp ((j : ℝ) * η))‖ ≤
        C * L ^ (-3 / 40 : ℝ) * paddingTiltNormalizer Q * ∏ i, primeHarmonicMass (P i) := by
  sorry

end OAI.TwoPointCorrelations
