-- Prove2me | Theorems.Thm_InducedMinorDeletion1657_Main_torso_treewidth
-- name    : InducedMinorDeletion1657.Main.torso_treewidth
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:34:58.542421+00:00
-- url     : https://prove2.me/theorems/19a31499-c574-440f-b1b1-a80f439fd8f3
-- title:
--   Lemma 3.9 — torso treewidth gluing
-- statement:
--   For a finite graph $G$ and any vertex subset $M$, let $G^+=\operatorname{Torso}(G,M)$. Then
--   $$\operatorname{tw}(G)\le\operatorname{tw}(G^+[M])+\operatorname{tw}(G-M)+1.$$
--   The exact additive one is retained. The restricted torso is used in the first term, while the torso operation itself keeps the whole vertex set. Empty $M$, full $M$, and empty $G$ are included. This is the width interface for combining a torso and its remaining components.
--
--   Formalization Note. The source's definition (a rooted tree, width $\max_x|\beta(x)|-1$) gives the empty graph treewidth $-1$, while Lean's `width` is nonnegative and gives it $0$. When $M=\emptyset$ or $V(G)\setminus M=\emptyset$ the source's $-1$ and $+1$ cancel, so the Lean statement adds the $+1$ only when both $M$ and $V(G)\setminus M$ are nonempty. This is the source's inequality on every instance (and also true under a treewidth-$0$ convention for the empty graph).
--
--   Differences from the source:
--   - encoding: arbitrary finite simple undirected graphs → graphs on Fin n, including n = 0; nonnegative treewidth from actual decompositions; reason: finite relabeling preserves every instance; empty treewidth zero changes no nonnegative-width predicate
--   - encoding: tw(∅) = −1 from the source's width max|β(x)| − 1, additive +1 always → Lean width(∅) = 0 and the additive term is 1 if M and V(G)∖M are both nonempty, else 0; reason: on every instance this is exactly the source's inequality under its −1 convention (the −1 and +1 cancel when one side is empty)
-- source:
--   Daniel Lokshtanov, Fahad Panolan, Saket Saurabh, Jie Xue, Meirav Zehavi, STOC 2027 submission #1657 (October 2026), p. 14 (PDF p. 15), Lemma 3.9

import Definitions.Def_InducedMinorDeletion1657_Main_Collections

set_option autoImplicit false
open Classical

namespace InducedMinorDeletion1657.Main

/-- Lemma 3.9, printed p. 14 / PDF p. 15. The source's treewidth of the empty graph is −1
    (a one-node decomposition with an empty bag), so when `M` or `V(G) ∖ M` is empty the
    source's `−1 + 1` cancels; with Lean's nonnegative `width` the `+1` is kept only when both
    `M` and its complement are nonempty, which is the source's inequality on every instance. -/
theorem torso_treewidth :
∀ (G : InputGraph) (M : Finset (Fin G.n)),
  width G.graph ≤ width ((torso G.graph M).induce (↑M : Set (Fin G.n))) +
    width (residual G.graph M) +
    (if M.Nonempty ∧ (Finset.univ \ M).Nonempty then 1 else 0) := by sorry

end InducedMinorDeletion1657.Main
