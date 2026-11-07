-- Prove2me | Theorems.Thm_LipStableCA_lemma_4_3
-- name    : LipStableCA.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:52:42.434621+00:00
-- url     : https://prove2.me/theorems/6d81d567-d55a-4b10-98c6-4b7efed18224
-- title:
--   Lemma 4.3 — Mechanism 2 is truthful in expectation
-- statement:
--   For every $0<\epsilon<1$ and every fixed order on the allocations, the random discount auction (Mechanism 2) is truthful in expectation.
--
--   For fixed discounts, the auction maximizes the expected welfare over a family of lotteries that does not depend on the reports, and its payments have the form of Fact 2.10.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 4.3, p.15

import Definitions.Def_LipStableCA_randomDiscount

namespace LipStableCA

/-- **Lemma 4.3.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.15. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. -/
theorem lemma_4_3 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) : (randomDiscount ord ϵ).IsTIE (discountSeedMeasure n m) := by sorry

end LipStableCA
