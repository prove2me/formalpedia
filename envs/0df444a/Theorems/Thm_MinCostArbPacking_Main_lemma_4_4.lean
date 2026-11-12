-- Prove2me | Theorems.Thm_MinCostArbPacking_Main_lemma_4_4
-- name    : MinCostArbPacking.Main.lemma_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T06:45:26.032203+00:00
-- url     : https://prove2.me/theorems/6f81dbb2-62bd-450e-810b-3768753b097a
-- title:
--   Lemma 4.4 — a shortest augmenting path stays in its tight block
-- statement:
--   **Lemma 4.4 (Localization to a tight block).** Assume the standing assumptions of §4.2. Let $u$ lie in a tight block $T\in\mathcal T(I)$ and let $P$ be a shortest augmenting path from $u$. All elements of $P$ except the last are internal to $T$, and the last element (the **terminal**) is a free arc entering $T$. Moreover $I'=I\oplus P$ is independent and
--
--   $$\deg^{in}_{I'}=\deg^{in}_I+\mathbf 1_u,\qquad |I'[T]|=|I[T]|=k(|T|-1).\tag{4.1}$$
--
--   Proposals from different blocks are therefore element-disjoint, and every old block stays tight.
--
--   Differences from the source:
--   - encoding: the standing assumptions of §3.1 and §4.2 (loops and arcs entering $r$ deleted; $I$ independent, cheapest for its indegree vector, no arc into $r$, indegree $\le k$) → explicit hypotheses `NoLoopNoRootArc` and `Standing`; reason: the source states them once for the whole section; they are hypotheses of every lemma there
-- source:
--   Zhaienhe Zhou, STOC 2027 submission #1416 (October 2026), §4.2.1, p.11, Lemma 4.4

import Mathlib
import Definitions.Def_MinCostArbPacking_Main_Exchange
set_option autoImplicit false

namespace MinCostArbPacking.Main

/-- Lemma 4.4 (Localization to a tight block), p.11, under the §4.2 standing assumptions: let `u`
lie in a tight block `T` and let `P` be a shortest augmenting path from `u`. All elements of `P`
except the last are internal to `T`, and the last is a free arc entering `T`; moreover `I' = I ⊕ P`
is independent, `deg^in_{I'} = deg^in_I + 1_u` and `|I'[T]| = |I[T]| = k(|T| - 1)`. -/
theorem lemma_4_4 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : Digraph V E) (k : ℕ) (hk : 1 ≤ k) (r : V) (c : E → ℝ)
    (hG : G.NoLoopNoRootArc r) (I : Finset E) (hI : G.Standing k r c I)
    (T : Finset V) (hT : G.IsTightBlock k I T) (u : V) (hu : u ∈ T) (P : List E)
    (hP : G.ShortestFrom k c I u P) :
    (∀ x ∈ P.dropLast, G.tail x ∈ T ∧ G.head x ∈ T) ∧
    (∀ e ∈ P.getLast?, G.Free k I e ∧ G.head e ∈ T ∧ G.tail e ∉ T) ∧
    G.IndepK k (symmDiff I P.toFinset) ∧
    (∀ v, G.inDeg (symmDiff I P.toFinset) v = G.inDeg I v + if v = u then 1 else 0) ∧
    (G.induced (symmDiff I P.toFinset) T).card = (G.induced I T).card ∧
    (G.induced I T).card = k * (T.card - 1) := by sorry

end MinCostArbPacking.Main
