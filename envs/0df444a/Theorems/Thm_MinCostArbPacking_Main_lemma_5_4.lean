-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_5_4
-- name    : MinCostArbPacking.Main.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:49:34.728491+00:00
-- url     : https://prove2.me/theorems/0e1eb724-8eaa-411d-a3d5-0455316e87ae
-- title:
--   Lemma 5.4 — adjusted distances and proposals by one Dijkstra run in $O(m+kn\log n\log(kn))$
-- statement:
--   **Lemma 5.4 (Computing adjusted distances and proposals).** Under (5.1) (with the indegree invariants and the reduced graph):
--
--   1. the distance from $v^\star$ to $z$ in the cyclic-scan $D_{\mathrm{cmp}}$ with weights $w_p$ is $\delta_v$;
--   2. one reverse Dijkstra computation from $z$, followed by path recovery, computes all $\delta_v$ and the proposals for the chosen vertices with finite distance in
--   $$O\big(m+kn\log n\log(kn)\big)$$
--   total time.
--
--   Formally, part 2 is one program and an absolute constant $C$: on every phase input satisfying the hypotheses, with at most one chosen deficient vertex per tight block, it outputs every $\delta_v$ (or $+\infty$) and a shortest augmenting path from every chosen $u$ with $\delta_u<\infty$, within $C(m+kn\log n\log(kn))$ steps.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §5.1 (loops and arcs entering $r$ deleted; no arc of $I$ into $r$, indegree $\le k$ elsewhere; the price invariant (5.1)) → explicit hypotheses `NoLoopNoRootArc`, `inDeg I r = 0`, `inDeg I v ≤ k` (v ≠ r), `PriceInv` (5.1), and the maintained forest decomposition (`ForestDecomp`; `DijkstraPre` in part 2); reason: the source states them once for §§3.1 and 5.1 (the algorithm keeps them); (5.1) implies that $I$ is cheapest for its indegree vector
--   - encoding: running time $O(f)$ in the model of §3.1 (exact arithmetic and comparisons in constant time) → one program of the unit-cost real RAM `Machine`, chosen before the input, halting within $C\cdot f$ executed instructions with an absolute constant $C$, for every word bound $W \ge (\mathrm{size}+2)^{c}$; reason: the standard reading of a deterministic time bound; the step count is intrinsic to the interpreter
--   - encoding: "the chosen vertices" → a set $U$ of deficient vertices with at most one in each tight block; reason: these are the vertices $u_T$ chosen in Algorithm 3
--   - encoding: the rooting of the forests used to build $D_{\mathrm{cmp}}$ → every valid rooting `ρ` (part 1); reason: the source's roots are arbitrary
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §5.4, p.25, Lemma 5.4

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_SearchGraph
import Definitions.Def_MinCostArbPacking_Main_IO
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 5.4 (Computing adjusted distances and proposals), p.25. (i) Under (5.1) (with the
indegree invariants), the distance from `v⋆` to `z` in the cyclic-scan `D_cmp` with the reduced
weights `w_p` is `δ_v`, for every rooting of the forests. (ii) One program (reverse Dijkstra from
`z` with path recovery) computes all `δ_v` and shortest augmenting paths from the chosen vertices
with finite `δ`, in `O(m + kn log n log(kn))` steps: at most `C·(m + k n log n log(kn))` for an
absolute constant `C`. -/
theorem lemma_5_4 :
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
      (hG : G.NoLoopNoRootArc r) (h : V → ℝ) (I : Finset E) (F : Fin k → Finset E)
      (hF : G.ForestDecomp k I F) (ρ : Fin k → V → Option E)
      (hρ : ∀ i, G.IsRooting (F i) (ρ i))
      (hr : G.inDeg I r = 0) (hdeg : ∀ v, v ≠ r → G.inDeg I v ≤ k) (hinv : G.PriceInv k c h I),
      ∀ v, walkDist (G.cmpSrc) (G.cmpTgt ρ) (G.cmpValid k .cyclic I F ρ)
          (G.cmpWp k .cyclic c h I F ρ) (.hd v) .sink = G.delta k c h I v) ∧
    (∃ (P : Machine.Program) (cw : ℕ) (C : ℝ), ∀ Y : PhaseInput, 1 ≤ Y.X.k → Y.DijkstraPre →
      ∀ W : ℤ, ((Y.X.size + 2 : ℕ) : ℤ) ^ cw ≤ W →
        Machine.HaltsWithin P W Y.inI Y.inRPrices
          (C * ((Y.X.m : ℝ) + Y.X.k * Y.X.n * logL Y.X.n * logL ((Y.X.k : ℝ) * Y.X.n)))
          (fun o or => Y.DijkstraOutput o or)) := by sorry

end MinCostArbPacking.Main
