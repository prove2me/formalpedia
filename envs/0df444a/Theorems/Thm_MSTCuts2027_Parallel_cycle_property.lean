-- Prove2me | Theorems.Thm_MSTCuts2027_Parallel_cycle_property
-- name    : MSTCuts2027.Parallel.cycle_property
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:47.532649+00:00
-- url     : https://prove2.me/theorems/9431f445-7240-4ac2-ba48-2c54aeb378c9
-- title:
--   Lemma 1 — cycle property (corrected: the graph must be connected)
-- statement:
--   Let $H$ be a finite connected simple graph with real edge capacities, $O$ a cycle in $H$, and $e$ a least-capacity edge of $O$. Then there is a maximum spanning tree of $H$ not containing $e$.
--
--   Capacities are arbitrary reals and ties are allowed. The assertion is about existence: not every maximum spanning tree need omit $e$. The cycle property justifies pruning edges of $G_1$.
--
--   Differences from the source:
--   - correction: H is any graph → H is connected; reason: a triangle plus an isolated vertex, all capacities 0, satisfies the printed hypotheses and has no spanning tree
-- source:
--   Baswana–Roy, Using MSTs to Compute All-Pairs Mincuts and Beyond ..., STOC 2027 submission #21, pinned preprint SHA-256 faa337be0f0f1bfbbcf924cb3591bd51ded2a6ef2c9e2154e00534a840156a11, Lemma 1, printed p. 5, PDF p. 7

import Mathlib
import Definitions.Def_FlowsNetworks_MultiTerminal_SpanningSubtree
import Definitions.Def_MSTCuts2027_Parallel_CutModel

namespace MSTCuts2027.Parallel

open FlowsNetworks.MultiTerminal

/-- Lemma 1, corrected: a finite connected graph with real capacities has a maximum spanning tree
avoiding any chosen least-capacity edge of any cycle. -/
theorem cycle_property {N : Type} [Fintype N] [DecidableEq N]
    (H : SimpleGraph N) (hH : H.Connected) (a : Sym2 N → ℝ)
    {w : N} (O : H.Walk w w) (hO : O.IsCycle)
    (e : Sym2 N) (he : e ∈ O.edges) (hmin : ∀ e' ∈ O.edges, a e ≤ a e') :
    ∃ T : SimpleGraph N, IsMaximalSpanningSubtree H T a ∧ e ∉ T.edgeSet := by sorry

end MSTCuts2027.Parallel
