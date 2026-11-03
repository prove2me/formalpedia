-- Prove2me | Theorems.Thm_MultiPurchaseMNL_claim_1
-- name    : MultiPurchaseMNL.claim_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:12:58.775985+00:00
-- url     : https://prove2.me/theorems/a8df8dfd-821e-4038-ac42-7c8429b5f7c4
-- title:
--   Claim 1 — removing a heavier product raises $\pi_m(i,\cdot)$ more
-- statement:
--   Let $S\subseteq[n]$ be an assortment and let $j,\ell\in S$ be two distinct products with $w_j\ge w_\ell$. Then for every product $i\in S\setminus\{j,\ell\}$ and every $m$,
--   $$
--   \pi_m(i,S_{-j})\ge\pi_m(i,S_{-\ell}).
--   $$
--   The choice probability of a product increases more when a more attractive product is removed. The claim is used in the lower-bound proof of Claim 3 (App. C.3).
--
--   Differences from the source:
--
--   - generalization: m ∈ [n] → every m : ℕ; reason: specializes; at m = 0 both sides are 0
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Claim 1, p.20 (proof App. C.1, p.40)

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Claim 1**, p.20: let `S ⊆ [n]` be
an assortment and `j, ℓ ∈ S` two distinct products with `wⱼ ≥ w_ℓ`; then for every product
`i ∈ S \ {j, ℓ}`, `πₘ(i, S−j) ≥ πₘ(i, S−ℓ)` for all `m ∈ [n]`.

**Formalization Note.** Stated for every `m : ℕ` (at `m = 0` both sides are `0`). -/
theorem claim_1 (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hw : ∀ i, 0 < I.w i) (S : Finset (Fin n)) (j ℓ : Fin n) (hj : j ∈ S) (hℓ : ℓ ∈ S)
    (hjℓ : j ≠ ℓ) (hwjℓ : I.w ℓ ≤ I.w j) (i : Fin n) (hi : i ∈ S) (hij : i ≠ j) (hiℓ : i ≠ ℓ)
    (m : ℕ) :
    piM μ I m i (S.erase ℓ) ≤ piM μ I m i (S.erase j) := by sorry

end MultiPurchaseMNL
