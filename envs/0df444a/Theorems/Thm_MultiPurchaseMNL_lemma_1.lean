-- Prove2me | Theorems.Thm_MultiPurchaseMNL_lemma_1
-- name    : MultiPurchaseMNL.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:12:58.668413+00:00
-- url     : https://prove2.me/theorems/2109ad37-5840-43ad-bc1d-191395d526dc
-- title:
--   Lemma 1 — the recursion for $\pi_m(i,S)$
-- statement:
--   For any assortment $S\subseteq[n]$, any product $i\in S$ and any $m\ge1$,
--   $$
--   \pi_m(i,S)=\frac{w_i}{1+w(S)}+\sum_{j\in S_{-i}}\frac{w_j}{1+w(S)}\,\pi_{m-1}(i,S_{-j}),
--   $$
--   where $\pi_m$ is the conditional choice probability (1) of the Multi-Purchase MNL model with standard Gumbel shocks, $w_i=e^{v_i}$ and $S_{-j}=S\setminus\{j\}$.
--
--   The recursion reduces every choice probability of the model to MNL-type ratios of weights. It is the basis of the exact evaluator of §2.2 and of the value function (4).
--
--   Differences from the source:
--
--   - generalization: m ∈ [n] → every m ≥ 1, written m + 1 for m : ℕ; reason: specializes to m ∈ [n]; avoids natural-number subtraction
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Lemma 1, p.11

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Lemma 1**, p.11: for any assortment
`S ⊆ [n]`, product `i ∈ S` and `m ∈ [n]`,
`πₘ(i, S) = wᵢ/(1 + w(S)) + Σ_{j∈S−i} wⱼ/(1 + w(S)) · πₘ₋₁(i, S−j)`.

**Formalization Note.** Written with `m + 1` for the paper's `m`, for every `m : ℕ`, so it covers
every `m ≥ 1` (the paper has `m ∈ [n]`) without natural-number subtraction. `πₘ` is (1) under the
product of standard Gumbel laws (`piM`), `wᵢ > 0` and `vᵢ = log wᵢ`. -/
theorem lemma_1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hw : ∀ i, 0 < I.w i) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (m : ℕ) :
    piM μ I (m + 1) i S =
      I.w i / (1 + wsum I S) +
        ∑ j ∈ S.erase i, I.w j / (1 + wsum I S) * piM μ I m i (S.erase j) := by sorry

end MultiPurchaseMNL
