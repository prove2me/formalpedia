-- Prove2me | Theorems.Thm_GoldbergTarjan_FIFO_source_reachable_of_pos_excess
-- name    : GoldbergTarjan.FIFO.source_reachable_of_pos_excess
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:34:55.118976+00:00
-- url     : https://prove2.me/theorems/70b29c3f-cc79-415c-a3a2-99cd3cacdb08
-- title:
--   Lemma 3.5 — from a vertex with positive excess the source is reachable in the residual graph
-- statement:
--   Let $f$ be a preflow on a flow network with source $s$, and let $v$ be a vertex with positive excess, $$e(v) = \sum_{u \in V} f(u,v) > 0.$$ Then the source $s$ is reachable from $v$ in the residual graph $G_f$: there is a directed path from $v$ to $s$ all of whose edges $(a,b)$ have positive residual capacity $r_f(a,b) = c(a,b) - f(a,b) > 0$.
--
--   This is what keeps the distance labels finite: Lemma 3.7 bounds the label of an active vertex along such a path.
--
--   **Formalization Note** Reachability is the reflexive–transitive closure of the residual-edge relation, so the case $v = s$ holds with the empty path.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 926, Lemma 3.5

import Mathlib
import Definitions.Def_GoldbergTarjan_FIFO_Network
import Definitions.Def_GoldbergTarjan_FIFO_PushRelabel
import Definitions.Def_GoldbergTarjan_FIFO_Algorithm
import Definitions.Def_GoldbergTarjan_FIFO_Counts

namespace GoldbergTarjan.FIFO

/-- Lemma 3.5 (Goldberg–Tarjan 1988, p. 926): if `f` is a preflow and `v` is a vertex with
positive excess, then the source `s` is reachable from `v` in the residual graph `G_f`. -/
theorem source_reachable_of_pos_excess {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (f : V → V → ℝ) (hf : IsPreflow N f) (v : V) (hv : 0 < excess f v) :
    ResidualReachable N f v N.s := by sorry

end GoldbergTarjan.FIFO
