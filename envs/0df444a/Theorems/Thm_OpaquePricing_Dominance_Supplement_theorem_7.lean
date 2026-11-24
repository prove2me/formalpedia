-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_theorem_7
-- name    : OpaquePricing.Dominance.Supplement.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T23:44:38.610595+00:00
-- url     : https://prove2.me/theorems/66614735-3aee-4d07-b1e8-cc886683b058
-- title:
--   Theorem 7 (corrected: direct-scan runtime) — both pricing optima and a distinct-candidate lower bound
-- statement:
--   Let $N\ge2$ be fixed, let $F$ be an exchangeable distribution represented by $m$ nonnegative valuation vectors with positive probabilities summing to one, and let $\alpha\in[0,1]$. Algorithm 1 is the defined backwards candidate tree followed by full-support revenue scans and a revenue-maximizing return. Denote the returned item-price vector by $p^{DP}$ and the size-price vector by $p^{OPQ}$. The corrected statement retains both global optimality conclusions:
--   $$R_{DP}(F,p^{DP})=\mathcal R_{DP}(F),\qquad R_{OPQ}^{\alpha}(F,p^{OPQ})=\mathcal R_{OPQ}^{\alpha}(F).$$
--   It also identifies the one-pass utility/price scan with the published DP payment and the weighted opaque reduction with the published expected OPQ revenue. Both returned price vectors are nonnegative; attainment is a conclusion about these actual returned vectors.
--
--   For the direct implementation described on p. 38, which scans every supported type at every candidate, the total cost of computing both optima, including the opaque-type reduction, satisfies
--   $$\forall N\ge2\ \exists C_N>0\ \forall m,F:\quad W_{DP+OPQ}(F)\le C_N m^{N+1}.$$
--   The printed exponent $N$ is corrected rather than assumed. For two items, a uniform exchangeable law on $2k$ distinct positive profiles yields at least $k^2$ distinct sorted candidate prices, requiring at least $2k^3$ type visits even after free deduplication. The theorem states the probability, exchangeability, distinctness, candidate count, work lower bound and its failure of every eventual $Cm^2$ bound. This refutes the claimed cost for the source's full-scan evaluation; it does not assert an impossibility result for other algorithms or accelerated shared evaluation. Arithmetic and comparisons are unit-cost real-RAM operations. These computational results are companions to the published goal.
--
--   Differences from the source:
--   - encoding: Algorithm 1 and its proof enumerate partial prices from the lowest coordinate and include an infinity no-purchase branch → the actual backwards list recursion uses a cap strictly above every supported value, discards negative critical prices, and returns the best scanned leaf; reason: the proof on p. 38 supplies the no-purchase branch missing from the box; the cap preserves its no-sale meaning using the published nonnegative real-price model
--   - encoding: Appendix D treats opaque values by size and both customer classes → the algorithm explicitly maximizes the published subset values by cardinality and uses weights αw and (1−α)w, including mixture endpoints; reason: preserves the common item price, size-uniform opaque prices and both published revenue functions
--   - correction: Theorem 7 claims total O(m^N) for Algorithm 1; its proof specifies a full linear revenue computation at every leaf → both global optima are retained, while the direct full-scan implementation has fixed-N O(m^(N+1)) total work and an exchangeable two-item distinct-candidate family rules out O(m^N) for that evaluation; reason: for m=2k, the profiles (b_l,l),(l,b_l), b_l=4k²+l(k+1), yield k² distinct sorted leaves (b_l−max(l−i,0),i); evaluating these by the specified type scan needs at least 2k³ visits, so the ratio to m² is at least k/2; this is an actual lower bound, independent of duplicate branches or padding; see DISPROOF.md
--   - generalization: Theorem 7 concerns exchangeable nonnegative support laws → the scan-payment identity covers every real profile at nonnegative prices, and the work upper bound covers every finite input table, while both optimum conclusions retain exchangeability; reason: the same utility/price fold gives the published payment even at negative valuations, and the loop counts depend on table sizes, not on symmetry; the finite representation also permits repeated profiles with their weights added
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Theorem 7, Algorithm 1 and proof, pp. 37–38

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Supplement_OpaqueAlgorithm

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Corrected direct-scan runtime of Algorithm 1, retaining BOTH global optima.
The lower bound concerns its specified full-support evaluation, not every conceivable
algorithm for computing optimal prices. The source's exact O(m^N) claim is not asserted. -/
theorem theorem_7 :
    (∀ {N m : ℕ}, 2 ≤ N → ∀ (F : FiniteTypes N m),
      Exchangeable (finiteLaw F) → ∀ α : ℝ, α ∈ Set.Icc 0 1 →
      (∀ p : Fin N → ℝ, (∀ i, 0 ≤ p i) → ∀ v : Fin N → ℝ,
        scanPayment v p = dpRevenue p v) ∧
      (∀ p : Fin N → ℝ, (∀ i, 0 ≤ p i) →
        ENNReal.ofReal (scanRevenue (reducedValues F) (reducedWeights F α) p) =
          expOPQ (finiteLaw F) α (treeItemPrice p) (treeSizePrice p)) ∧
      (∀ i, 0 ≤ algorithmDP F i) ∧
      expDP (finiteLaw F) (algorithmDP F) = optDP (finiteLaw F) ∧
      (∀ i, 0 ≤ algorithmOPQ F α i) ∧
      expOPQ (finiteLaw F) α (treeItemPrice (algorithmOPQ F α))
        (treeSizePrice (algorithmOPQ F α)) = optOPQ (finiteLaw F) α) ∧
    (∀ N : ℕ, 2 ≤ N → ∃ C : ℝ, 0 < C ∧
      ∀ (m : ℕ) (F : FiniteTypes N m),
        (bothPricingWork F : ℝ) ≤ C * (m : ℝ)^(N + 1)) ∧
    (∀ k : ℕ, 1 ≤ k →
      IsProbabilityMeasure (runtimeLaw k) ∧ Exchangeable (runtimeLaw k) ∧
      Function.Injective (runtimeValues k) ∧
      (∀ j i, 0 ≤ runtimeValues k j i) ∧
      k^2 ≤ (priceTree (runtimeValues k) 2).toFinset.card ∧
      2 * k^3 ≤ distinctScanWork k ∧
      distinctScanWork k ≤ enumerationWork (runtimeValues k)) ∧
    (∀ C : ℝ, 0 < C → ∀ K : ℕ, ∃ k : ℕ, max 1 K ≤ k ∧
      C * (2 * k : ℝ)^2 < (distinctScanWork k : ℝ)) := by sorry

end OpaquePricing.Dominance.Supplement
