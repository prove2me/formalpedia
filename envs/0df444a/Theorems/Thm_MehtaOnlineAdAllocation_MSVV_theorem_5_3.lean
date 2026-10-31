-- Prove2me | Theorems.Thm_MehtaOnlineAdAllocation_MSVV_theorem_5_3
-- name    : MehtaOnlineAdAllocation.MSVV.theorem_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T15:39:11.270386+00:00
-- url     : https://prove2.me/theorems/e17f44dc-4f64-4561-a165-1d081565d0f6
-- title:
--   Theorem 5.3 — optimal small-bids competitiveness of MSVV
-- statement:
--   Let $c=1-\exp(-1)$. MSVV attains limiting competitive ratio $c$ on arbitrary finite Adwords instances with arbitrary positive real budgets, and this is optimal even among randomized online algorithms.
--
--   **Performance.** For every $\varepsilon>0$ there exists $\eta>0$ such that, for every finite instance with $b_{ut}\le\eta B_u$, every run $\sigma$ of the exact capped exponential MSVV rule and every offline allocation $\tau$ satisfy
--   $$\mathrm{rev}(\sigma)\ge(c-\varepsilon)\mathrm{rev}(\tau).$$
--   The threshold is independent of all instance data, sizes and tie-breaking. Payments are capped at remaining budget; no full-budget optimum is required. Empty inputs have zero revenue, so the inequality needs no division by OPT and no additive loss.
--
--   **Randomized optimality.** For every $\varepsilon>0$, $\eta>0$ and family $A_{N,B}$ of arbitrary randomized causal policies on finite binary histories, there exist positive integers $N,B$ with $1\le\eta B$, a fixed binary-bid instance of length $NB$ with common budget $B$, and an allocation achieving revenue $NB$, such that
--   $$\mathbb E_{A_{N,B}}[\mathrm{ALG}]\le(c+\varepsilon)NB.$$
--   No allocation can exceed $NB$, so this is a positive offline optimum, and every bid-to-budget ratio is at most $\eta$. The instance is chosen after the policy family and before the random coins. Any randomized algorithm on general real inputs, including one with continuous internal randomness, restricts to a distribution on the finite deterministic history policies for each $N,B$; no finite-support assumption is made on full real-input policies. The already proved AdWordsMSVV.LowerBound.theorem_9 supplies this clause and is referenced separately as support.
--
--   Differences from the source:
--   - reading: MSVV achieves 1-1/e under infinitesimally small bids → a uniform epsilon-eta performance guarantee and arbitrarily small-bid randomized obstructions; reason: pp. 307, 312–315 and 326 use a small-bid limit rather than a finite-bid exact constant
--   - encoding: finite advertisers and query occurrences → Fin N and Fin M with an Option-valued allocation; reason: enumeration preserves every finite instance and arrival order
--   - encoding: nonnegative budgets and explicit graph edges → positive budgets and zero entries for nonedges; reason: zero-budget vertices and zero-payment assignments can be deleted with no change to any payment or future availability
--   - encoding: comparison with the capped integral offline optimum → comparison with every allocation using capped revenue; reason: the finite nonempty set of allocations has a maximizing member, and zero entries can be erased to obtain graph feasibility
--   - encoding: arbitrary randomized online algorithms and a hard input independent of their coins → arbitrary families of PMFs on finite deterministic binary-history policies, with a hard input chosen after the family; reason: restriction of any randomized causal algorithm to each finite binary decision tree induces such a PMF, including continuous coins, and common integer budgets can be made arbitrarily large
--   - encoding: no better limiting competitive ratio on general Adwords inputs → positive-optimum binary hard instances with 1 at most eta times B; reason: an existential hard subfamily is sufficient for the full impossibility claim, and the referenced theorem covers every integer budget
-- source:
--   Aranyak Mehta, Online Matching and Ad Allocation, Foundations and Trends in Theoretical Computer Science 8(4), 265–368, 2013, DOI 10.1561/0400000057 (published), Theorem 5.3, printed p. 312 (PDF p. 50), with §5.1 small bids, p. 307 (PDF p. 45), Algorithm 10 p. 311 (PDF p. 49), capping p. 308 (PDF p. 46), competitive ratio pp. 279–280 (PDF pp. 17–18), and the infinitesimal integral discussion p. 326 (PDF p. 64).

import Definitions.Def_MehtaOnlineAdAllocation_MSVV_IsRun
import Definitions.Def_MehtaOnlineAdAllocation_MSVV_SmallBids
import Definitions.Def_AdWordsMSVV_LowerBound_Setting

namespace MehtaOnlineAdAllocation.MSVV

theorem theorem_5_3 :
    (∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧
      ∀ (N M : ℕ) (I : Instance N M), SmallBids I η →
      ∀ σ : Allocation N M, IsRun I σ → ∀ τ : Allocation N M,
        (1 - Real.exp (-1) - ε) * revenue I τ ≤ revenue I σ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ η : ℝ, 0 < η →
      ∀ A : (N B : ℕ) → AdWordsMSVV.LowerBound.RandAlg N (N * B),
      ∃ N B : ℕ, 0 < N ∧ 1 ≤ B ∧ 1 ≤ η * (B : ℝ) ∧
      ∃ (I : AdWordsMSVV.LowerBound.Instance N (N * B))
        (τ : Fin (N * B) → Option (Fin N)),
        AdWordsMSVV.LowerBound.offlineRevenue B I τ = N * B ∧
        AdWordsMSVV.LowerBound.expectedRevenue B I (A N B) ≤
          (1 - Real.exp (-1) + ε) * ((N : ℝ) * (B : ℝ))) := by sorry

end MehtaOnlineAdAllocation.MSVV
