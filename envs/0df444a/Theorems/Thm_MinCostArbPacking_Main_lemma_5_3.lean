-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_5_3
-- name    : MinCostArbPacking.Main.lemma_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:33.42421+00:00
-- url     : https://prove2.me/theorems/a1db7618-eb67-4155-ad46-567418fc3f39
-- title:
--   Lemma 5.3 — a feasible potential on $D_{\mathrm{cmp}}$
-- statement:
--   **Lemma 5.3 (A feasible potential).** Under (5.1) (with $\deg^{in}_I(r)=0$, indegrees $\le k$ and the reduced graph), for the cyclic-scan $D_{\mathrm{cmp}}$ and the potential $p$ of (5.6), all reduced weights
--
--   $$w_p(x,y)=w(x,y)-p(x)+p(y)$$
--
--   are nonnegative. In particular, $D_{\mathrm{cmp}}$ has no negative cycle.
--
--   This makes Dijkstra's algorithm applicable.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §5.1 (loops and arcs entering $r$ deleted; no arc of $I$ into $r$, indegree $\le k$ elsewhere; the price invariant (5.1)) → explicit hypotheses `NoLoopNoRootArc`, `inDeg I r = 0`, `inDeg I v ≤ k` (v ≠ r), `PriceInv` (5.1), and the maintained forest decomposition `ForestDecomp` (§4.2, §4.3); reason: the source states them once for §§3.1 and 5.1 (the algorithm keeps them); (5.1) implies that $I$ is cheapest for its indegree vector
--   - encoding: the rooting of the forests → every valid rooting `ρ`; reason: the source's roots are arbitrary
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §5.3, p.25, Lemma 5.3

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 5.3 (A feasible potential), p.25: under (5.1) (with the indegree invariants), all reduced
weights `w_p` of the cyclic-scan `D_cmp` with the potential (5.6) are nonnegative; in particular
`D_cmp` has no negative cycle. -/
theorem lemma_5_3 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (h : V → ℝ) (I : Finset E) (F : Fin k → Finset E)
    (hF : G.ForestDecomp k I F) (ρ : Fin k → V → Option E) (hρ : ∀ i, G.IsRooting (F i) (ρ i))
    (hr : G.inDeg I r = 0) (hdeg : ∀ v, v ≠ r → G.inDeg I v ≤ k) (hinv : G.PriceInv k c h I) :
    (∀ a, G.cmpValid k .cyclic I F ρ a → 0 ≤ G.cmpWp k .cyclic c h I F ρ a) ∧
    ¬ HasNegCycle (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k .cyclic I F ρ) (Digraph.cmpW c) := by sorry

end MinCostArbPacking.Main
