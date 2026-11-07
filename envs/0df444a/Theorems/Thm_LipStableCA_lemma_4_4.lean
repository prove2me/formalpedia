-- Prove2me | Theorems.Thm_LipStableCA_lemma_4_4
-- name    : LipStableCA.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:51:05.5577+00:00
-- url     : https://prove2.me/theorems/4cf1a771-d4a6-4736-9ee9-9d5f67b31d90
-- title:
--   Lemma 4.4 — Mechanism 2 is ex-post IR with nonnegative payments
-- statement:
--   For every $0<\epsilon<1$ and every fixed order on the allocations, the random discount auction is ex-post individually rational, and its payments are nonnegative.
--
--   A truthful bidder's realized utility is nonnegative for every realization of the discounts.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal A$ fixed before the reports are seen → an explicit `LinearOrder` parameter, for every order; reason: Lean convention; same instances
--   - encoding: for every realization of the discounts (printed proof) → with probability one over the seed law; reason: the statement is ex-post IR of Definition 2.1; realizations outside $U\in[0,1]$ have probability zero
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 4.4, p.15

import Definitions.Def_LipStableCA_randomDiscount
open MeasureTheory

namespace LipStableCA

/-- **Lemma 4.4.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.15. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. an explicit `LinearOrder` parameter, for every order: Lean convention; same instances. with probability one over the seed law: the statement is ex-post IR of Definition 2.1; realizations outside `U∈[0,1]` have probability zero. -/
theorem lemma_4_4 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Alloc n m)) {ϵ : ℝ} (h0 : 0 < ϵ)
    (h1 : ϵ < 1) :
    (randomDiscount ord ϵ).IsExPostIR (discountSeedMeasure n m) ∧
      ∀ v : Profile n m, IsProfile v → ∀ i, ∀ᵐ ω ∂(discountSeedMeasure n m),
        0 ≤ (randomDiscount ord ϵ).pay v ω i := by sorry

end LipStableCA
