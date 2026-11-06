-- Prove2me | Theorems.Thm_LogStarBinPacking_claim_2_1
-- name    : LogStarBinPacking.claim_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:31:25.263039+00:00
-- url     : https://prove2.me/theorems/c6ca64b5-1ed3-4373-a4fe-2528c6c064fb
-- title:
--   Claim 2.1 — $|J|=3M$, $p_1(J)=0$ and the size window
-- statement:
--   Let $I$ be a bin packing instance with $n$ items, $b\ge1$ an integer, $V$ a finite set with $|V|\ge n+b$, $h:V\to[0,1]\cap\mathbb Q$ and $\varepsilon>0$ rational. Let $J$ be the three-item instance of the proof of Lemma 2.1, with sizes $s_J$ and scores $p_1,p_2$, and $M=|V|+b$.
--   Then
--   $$
--   |J|=3M,\qquad p_1(J)=0,
--   $$
--   and every item $u\in J$ satisfies
--   $$
--   s_J(u)\in\Big(\frac13-\varepsilon,\frac13+\varepsilon\Big)\cap\Big(\frac14,\frac12\Big).
--   $$
--
--   The count and the zero total type score are what force a packing with few extra bins to consist mostly of type-zero triples.
--
--   Differences from the source:
--   - encoding: indices 1 ≤ r ≤ f and 1 ≤ j ≤ b of the filler and endpoint items → 0-based indices in Fin f and Fin b; reason: relabelling; the same items and sizes
-- source:
--   I. Doron-Arad, Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin, manuscript (sha256 1d88425d…), Claim 2.1, p.5

import Mathlib
import Definitions.Def_BinPackingGap
import Definitions.Def_LogStarBinPacking_ThreeItem

namespace LogStarBinPacking

open OAI.BinPackingGap

/-- **Claim 2.1.** Doron-Arad, *Additive Ω(log∗ OPT) Gap for Bin Packing with Three Items per Bin*, manuscript (sha256 1d88425d…), Claim 2.1, p.5.
For the instance `J` built in the proof of Lemma 2.1 from `(I, b, V, h, ε)`:
`|J| = 3M` with `M = |V| + b`, `p₁(J) = 0`, and every size lies in
`(1/3 − ε, 1/3 + ε) ∩ (1/4, 1/2)`.

**Formalization Note** The standing data of Lemma 2.1 are binders: `b ≥ 1`, a finite set `V`,
`h : V → [0, 1] ∩ ℚ`, a rational `ε > 0`, `|V| ≥ |I| + b`. The items of `J` are
`JItem I V b`, the scores and sizes are (2.3)–(2.5). -/
theorem claim_2_1 (I : Instance) (b : ℕ) (hb : 1 ≤ b) (V : Type*) [Fintype V] [DecidableEq V]
    (h : V → ℚ) (h0 : ∀ v, 0 ≤ h v) (h1 : ∀ v, h v ≤ 1) (ε : ℚ) (hε : 0 < ε)
    (hV : I.n + b ≤ Fintype.card V) :
    Fintype.card (JItem I V b) = 3 * (Fintype.card V + b) ∧
    ∑ u : JItem I V b, ThreeItem.typeScore u = 0 ∧
    ∀ u : JItem I V b,
      1 / 3 - ε < ThreeItem.size I.size h ε u ∧ ThreeItem.size I.size h ε u < 1 / 3 + ε ∧
      1 / 4 < ThreeItem.size I.size h ε u ∧ ThreeItem.size I.size h ε u < 1 / 2 := by sorry

end LogStarBinPacking
