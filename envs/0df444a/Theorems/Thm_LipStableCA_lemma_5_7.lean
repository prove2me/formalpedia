-- Prove2me | Theorems.Thm_LipStableCA_lemma_5_7
-- name    : LipStableCA.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:55:25.997879+00:00
-- url     : https://prove2.me/theorems/eb5c144a-86e1-47d7-9e88-00352c9042ae
-- title:
--   Lemma 5.7 — Mechanism 3 is universally truthful and ex-post IR
-- statement:
--   The random block auction (Mechanism 3) is universally truthful and ex-post individually rational, for every fixed order used in its runs of Mechanism 1.
--
--   Differences from the source:
--   - encoding: $m,n\ge 1$ throughout (§5 says so; Mechanism 2 has $U^{1/m}$) → the hypothesis `1 ≤ m`; reason: the paper's standing setting; excludes only the empty item set
--   - encoding: a total order on $\mathcal F_Q$ in each run → one `LinearOrder` on sets of bidders, for every such order; reason: its restriction to each $\mathcal F_Q$ is the fixed order of that run
--   - encoding: the paper does not name a σ-algebra on the seed space → measurability of the rule stated as a clause or a hypothesis; reason: this is what makes the allocation law meaningful (paper.md decision 3)
-- source:
--   Afshinmehr, Koutsoupias, Lipschitz Stable Combinatorial Auctions, STOC 2027 submission (manuscript sha256 c5e4c53f…), Lemma 5.7, p.25

import Definitions.Def_LipStableCA_randomBlock

namespace LipStableCA

/-- **Lemma 5.7.** Afshinmehr, Koutsoupias, *Lipschitz Stable Combinatorial Auctions*, STOC 2027 submission (manuscript sha256 c5e4c53f…), p.25. **Formalization Note.** the hypothesis `1 ≤ m`: the paper's standing setting; excludes only the empty item set. one `LinearOrder` on sets of bidders, for every such order: its restriction to each `F_Q` is the fixed order of that run. measurability of the rule stated as a clause or a hypothesis: this is what makes the allocation law meaningful (paper.md decision 3). -/
theorem lemma_5_7 {n m : ℕ} (hm : 1 ≤ m) (ord : LinearOrder (Finset (Fin n))) :
    (randomBlock ord : Mechanism n m (BlockSeed n m)).Measurable ∧
    (randomBlock ord : Mechanism n m (BlockSeed n m)).PayMeasurable ∧
    (randomBlock ord : Mechanism n m (BlockSeed n m)).IsUT (blockMeasure n m) ∧
    (randomBlock ord : Mechanism n m (BlockSeed n m)).IsExPostIR (blockMeasure n m) := by sorry

end LipStableCA
