-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_max_flow_iff_no_augmenting_path
-- name    : GoldbergTarjan.Generic.max_flow_iff_no_augmenting_path
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:26:34.80798+00:00
-- url     : https://prove2.me/theorems/941659f2-e12e-4fb0-a88e-ddbb4aec8121
-- title:
--   Theorem 3.2 (Ford–Fulkerson) — a flow is maximum iff t is not reachable from s in the residual graph
-- statement:
--   Let $N$ be a flow network with source $s$ and sink $t$, and let $f$ be a flow (capacity, antisymmetry and conservation constraints). An **augmenting path** is a simple path from $s$ to $t$ in the residual graph $G_f$. Then
--
--   $$f \text{ is a maximum flow} \iff \text{there is no augmenting path, i.e. } t \text{ is not reachable from } s \text{ in } G_f.$$
--
--   This is the classical theorem of Ford and Fulkerson, which the paper cites without proof; together with Lemma 3.3 it yields the correctness of the algorithm (Theorem 3.4).
--
--   **Formalization Note.** Flows here are antisymmetric real functions on all vertex pairs, as in the paper, not nonnegative arc flows.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 926, Theorem 3.2 (citing Ford and Fulkerson [7])

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Preflow

namespace GoldbergTarjan.Generic

/-- Theorem 3.2 (Ford–Fulkerson; Goldberg–Tarjan 1988, p. 926). A flow `f` is maximum if and
only if there is no augmenting path, that is, `t` is not reachable from `s` in `G_f`. -/
theorem max_flow_iff_no_augmenting_path {V : Type} [Fintype V]
    (N : Network V) (f : V → V → ℝ) (hf : IsFlow N f) :
    IsMaxFlow N f ↔ ¬ ResidualReachable N f N.s N.t := by sorry

end GoldbergTarjan.Generic
