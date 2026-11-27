-- Prove2me | Theorems.Thm_OpaquePricing_Dominance_Supplement_lemma_10
-- name    : OpaquePricing.Dominance.Supplement.lemma_10
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-23T23:42:41.224069+00:00
-- url     : https://prove2.me/theorems/13909249-1f94-4c1d-a7d9-1e65643f3a1b
-- title:
--   Lemma 10 — Finite-type critical prices (corrected: canonical equal-price ties)
-- statement:
--   Let $F$ have $m$ nonnegative valuation vectors $v_j$ with strictly positive weights summing to one. Let $p\ge0$ maximize its weighted item-pricing revenue among all nonnegative price vectors, and suppose $p_1\ge\cdots\ge p_N$, where $N\ge2$. Among utility-maximizing options the buyer selects the highest price, and among remaining equal-price ties the smallest item index. For every $i$,
--   $$\left[\exists j,\ p_i=v_{j,i}-\max\left(\{0\}\cup\{(v_{j,k}-p_k)^+:k>i\}\right)\right]\quad\text{or}\quad\left[\text{no type buys item }i\right].$$
--   The outside utility is zero when the cheaper-index set is empty. This finite-type structural result supports Theorem 6. Its optimization and revenue are the same for every permitted equal-price tie choice; the correction concerns the identity of the bought item, not a restriction on valuation laws or prices.
--
--   Differences from the source:
--   - encoding: items 1 through N with N at least 2 → Fin N with the explicit premise 2 ≤ N; reason: zero-based indices preserve the full selling-model domain
--   - encoding: a distribution over m customer types and a revenue optimal price vector → positive type weights summing to one, weighted published DP revenue, and an explicit comparison with every nonnegative price vector; reason: support types have positive probability by definition, and global optimality is the source hypothesis
--   - correction: arbitrary equal-price ties in §2 together with Lemma 10’s item-specific no-purchase alternative → smallest-index refinement among equal-utility highest-price winners; reason: at weights 3/4 for (1,0) and 1/4 for (2,2), p=(1,1) is optimal, yet a permitted tie choosing item 2 for (2,2) violates the source conclusion for i=2; canonical ties repair this without excluding any valuation law or price vector; see DISPROOF.md, PDF pp. 8 and 54
-- source:
--   Elmachtoub & Hamilton, The Power of Opaque Products in Pricing, author's manuscript (2021; Manag. Sci. doi:10.1287/mnsc.2020.3750), Lemma 10, p. 54

import Mathlib
import Definitions.Def_OpaquePricing_Dominance_Setting
import Definitions.Def_OpaquePricing_Dominance_Supplement_FiniteTypes

open MeasureTheory

namespace OpaquePricing.Dominance.Supplement

/-- Equal-price utility ties are resolved towards the smallest index, preserving revenue. -/
theorem lemma_10 {N m : ℕ} (hN : 2 ≤ N) (F : FiniteTypes N m)
    (p : Fin N → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hsort : ∀ i k, i ≤ k → p k ≤ p i)
    (hopt : ∀ q : Fin N → ℝ, (∀ i, 0 ≤ q i) → finiteRevenue F q ≤ finiteRevenue F p) :
    ∀ i, (∃ j, p i = F.values j i - cheaperUtility p (F.values j) i) ∨
      (∀ j, ¬ buys p (F.values j) i) := by sorry

end OpaquePricing.Dominance.Supplement
