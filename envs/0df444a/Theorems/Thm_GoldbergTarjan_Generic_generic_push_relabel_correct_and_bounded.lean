-- Prove2me | Theorems.Thm_GoldbergTarjan_Generic_generic_push_relabel_correct_and_bounded
-- name    : GoldbergTarjan.Generic.generic_push_relabel_correct_and_bounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:31:12.781457+00:00
-- url     : https://prove2.me/theorems/aca8ba14-3c9c-407b-8b21-7a6c89b09e82
-- title:
--   Theorems 3.11 and 3.4 — the generic push-relabel algorithm stops within $(2n-1)(n-2) + 2nm + 4n^2m$ basic operations with a maximum flow
-- statement:
--   Let $N$ be a flow network with $n$ vertices and $m$ edges satisfying the standing assumption $m \ge n - 1$, and let $(f_0,d_0), \dots, (f_K,d_K)$ be any execution of the generic push-relabel algorithm: it starts from the preflow saturating the source edges with the simple labeling ($d(s)=n$, $d(v)=0$ otherwise), and each step applies one applicable push or relabel, in any order. Then
--
--   1. the number of basic operations is bounded:
--   $$K \le (2n-1)(n-2) + 2nm + 4n^2 m;$$
--   2. if no basic operation is applicable in the final state $(f_K,d_K)$, then $f_K$ is a maximum flow.
--
--   Part 1 is Theorem 3.11 ("The generic algorithm terminates after $O(n^2m)$ basic operations") with the explicit constants of Lemmas 3.8, 3.9 and 3.10, from which the paper says it is immediate: every basic operation is a relabeling, a saturating push or a nonsaturating push. Since every run has length at most this bound, the algorithm cannot run forever, whatever order of operations is chosen. Part 2 is Theorem 3.4, the correctness of the algorithm.
--
--   **Formalization Note.** Theorem 3.4 assumes that all labels are finite at termination; that hypothesis is dropped here because Lemma 3.7 ($d(v) \le 2n-1$ throughout) discharges it. "Terminates" is the negation of the loop guard of Fig. 2 (no push and no relabel applies), not "no active vertex". The bound is $O(n^2m)$ in the paper, explicit from Lemmas 3.8–3.10.
-- source:
--   Goldberg, Tarjan, A New Approach to the Maximum-Flow Problem, J. ACM 35(4), 1988, p. 928, Theorem 3.11 (with Lemmas 3.8–3.10, pp. 927–928) and p. 926, Theorem 3.4

import Mathlib
import Definitions.Def_GoldbergTarjan_Generic_Run

namespace GoldbergTarjan.Generic

/-- Theorem 3.11 with Theorem 3.4 (Goldberg–Tarjan 1988, pp. 928 and 926). Under the standing
assumption `m ≥ n - 1` (p. 923), every execution of the generic push-relabel algorithm (started
with the simple labeling, basic operations applied in any order) performs at most
`(2n - 1)(n - 2) + 2nm + 4n²m` basic operations — `O(n²m)` in the paper, explicit from
Lemmas 3.8–3.10 — and, if no basic operation applies at its end, the final preflow is a
maximum flow. -/
theorem generic_push_relabel_correct_and_bounded {V : Type} [Fintype V] [DecidableEq V]
    (N : Network V) (hm : Fintype.card V - 1 ≤ N.numEdges)
    (σ : ℕ → State V) (K : ℕ) (hrun : IsRun N σ K) :
    K ≤ (2 * Fintype.card V - 1) * (Fintype.card V - 2) +
        2 * Fintype.card V * N.numEdges + 4 * Fintype.card V ^ 2 * N.numEdges ∧
      (NoBasicOpApplicable N (σ K) → IsMaxFlow N (σ K).1) := by sorry

end GoldbergTarjan.Generic
