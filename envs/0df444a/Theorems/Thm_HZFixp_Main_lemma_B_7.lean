-- Prove2me | Theorems.Thm_HZFixp_Main_lemma_B_7
-- name    : HZFixp.Main.lemma_B_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:53:58.094891+00:00
-- url     : https://prove2.me/theorems/0b6af09e-9d87-4c3b-a68b-74fb02ab20ca
-- title:
--   Lemma B.7 — cross-node consumption: Z_i ≤ q_i and Σ Z_i ≤ W
-- statement:
--   Let $(X,p)$ be an HZ equilibrium of the market of §3.4.1 built from a Reciprocal VI instance with $W$ unit edges. Let $Z_i$ be the quantity of other nodes' goods (low or high goods of nodes $j\ne i$) consumed by the node-$i$ agents, and $q_i$ the quantity of node-$i$ goods consumed by the edge agents. Then
--   $$Z_i\le q_i\ \text{ for every node } i,\qquad \sum_i Z_i\le W .$$
--
--   The bound leaves every low group enough supply for its own node agents, which makes the low-price inequalities of Lemma B.6 tight.
--
--   Differences from the source:
--   - encoding: the market's N agents and N goods in construction order → typed agents MAgent and goods MGood (node agents by node and copy, edge agents by edge; low goods by group and copy, high goods by node and copy, reference goods); equilibria are CardinalMatching.IsApproxHZ at ε = 0 over these types; reason: a relabelling of rows and columns; the lemmas do not depend on the order
--   - reading: at the normalized prices → no prices in the statement; reason: Z_i and q_i depend on the allocation only
-- source:
--   Liu, Tao, Yan, Settling the Complexity of Hylland–Zeckhauser Equilibria, arXiv:2606.06317 (held version later than v2, sha256 36e91522…af1c), p. 59 (PDF 61), Lemma B.7

import Mathlib
import Definitions.Def_CardinalMatching_IsApproxHZ
import Definitions.Def_HZFixp_Main_ReciprocalVI
import Definitions.Def_HZFixp_Main_Market

namespace HZFixp.Main

/-- **Lemma B.7.** At every equilibrium of the market of §3.4.1, `Z_i ≤ q_i` for every node and
`∑_i Z_i ≤ W`, where `Z_i` is the quantity of other nodes' goods consumed by node-`i` agents and
`q_i` the quantity of node-`i` goods consumed by edge agents. -/
theorem lemma_B_7 (I : RVIInst) (X : MAgent I.1 → MGood I.1 → ℝ) (p : MGood I.1 → ℝ)
    (hX : CardinalMatching.IsApproxHZ I.1.mUtil 0 X p) :
    (∀ i, I.1.Zq X i ≤ I.1.qq X i) ∧ ∑ i, I.1.Zq X i ≤ (I.1.W : ℝ) := by sorry

end HZFixp.Main
