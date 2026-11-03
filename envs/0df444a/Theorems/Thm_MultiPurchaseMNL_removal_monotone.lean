-- Prove2me | Theorems.Thm_MultiPurchaseMNL_removal_monotone
-- name    : MultiPurchaseMNL.removal_monotone
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:12.34508+00:00
-- url     : https://prove2.me/theorems/8f28541c-f812-47c8-99a4-de51ff96e676
-- title:
--   §4.4, p.21 — removing a product cannot lower $\pi_m(i,\cdot)$
-- statement:
--   For every $m$, every assortment $S$, every product $i\in S$ and every other product $\ell\in S_{-i}$,
--   $$
--   \pi_m(i,S)\le\pi_m(i,S_{-\ell}).
--   $$
--   In the paper's words, "adding any product $\ell$ to $Q$ can only reduce the choice probability of product $i$". It is the first inequality of part (ii) of the upper-bound proof of Claim 3.
--
--   Differences from the source:
--
--   - generalization: ℓ ∈ L ∩ Q₋ᵢ in the setting of Claim 3, standard Gumbel shocks → every assortment S, every ℓ ∈ S − i, every m : ℕ, every i.i.d. shock law μ and every weight vector; reason: removing ℓ lowers rank(i, ·) shock by shock; the paper's case is a special one
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §4.4, p.21, "adding any product ℓ ∈ L ∩ Q−i to Q can only reduce the choice probability of product i"

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §4.4, p.21, proof of Claim 3, part
(ii): "adding any product `ℓ ∈ L ∩ Q−i` to `Q` can only reduce the choice probability of product
`i`". For every `m`, every assortment `S`, every `i ∈ S` and every `ℓ ∈ S − i`,
`πₘ(i, S) ≤ πₘ(i, S − ℓ)`.

**Formalization Note.** Stated for every `m : ℕ`, every assortment and every `ℓ ≠ i` in it, not only
light `ℓ`; and for every i.i.d. shock law `μ` and every weight vector (the inclusion of events
holds shock by shock). -/
theorem removal_monotone (μ : Measure ℝ) [IsProbabilityMeasure μ] {n mmax : ℕ}
    (I : Instance n mmax) (m : ℕ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (ℓ : Fin n)
    (hℓ : ℓ ∈ S.erase i) :
    piM μ I m i S ≤ piM μ I m i (S.erase ℓ) := by sorry

end MultiPurchaseMNL
