-- Prove2me | Theorems.Thm_McNaughtonSched_SingleProc_pair_interchange
-- name    : McNaughtonSched.SingleProc.pair_interchange
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:59:32.837084+00:00
-- url     : https://prove2.me/theorems/2808e6ab-834b-4aac-a0ec-3ec7e392ad58
-- title:
--   Theorem 2.1 — after both deadlines, doing (i) before (j) loses less when $r_i > r_j$
-- statement:
--   Let $(i)$ and $(j)$ be two tasks with processing times $a_i, a_j > 0$, penalties $p_i, p_j$ and deadlines $d_i, d_j$, and write $r_i = p_i/a_i$, $r_j = p_j/a_j$. Suppose the two tasks occupy the $a_i + a_j$ consecutive units of time starting at a time $t$ with $d_i \le t$ and $d_j \le t$. With $\ell_k(s) = p_k \max(0, s - d_k)$ the loss on task $(k)$ completed at time $s$: if $r_i > r_j$, then
--
--   $$
--   \ell_i(t + a_i) + \ell_j(t + a_i + a_j) \;<\; \ell_j(t + a_j) + \ell_i(t + a_j + a_i).
--   $$
--
--   The left side is the loss on $(i)$ and $(j)$ when $(i)$ is done first, the right side when $(j)$ is done first.
--
--   This is the adjacent-interchange step on which the ratio rule rests: after both deadlines have passed, swapping two consecutive tasks into order of decreasing $r$ strictly lowers their joint loss.
--
--   **Formalization Note** Only the two tasks' own losses are compared; the common loss "computed as far as time $t$" in the paper cancels. No sign condition on the penalties is assumed (the page has none, and none is needed); $a_i, a_j > 0$ is the model's standing assumption that tasks take time, needed for $r = p/a$ to be meaningful. The hypothesis $r_i > r_j$ forces $(i) \ne (j)$.
-- source:
--   McNaughton, Scheduling with Deadlines and Loss Functions, Management Science 6(1), 1959, p. 4, Theorem 2.1

import Mathlib
import Definitions.Def_McNaughtonSched_SingleProc_Model

namespace McNaughtonSched.SingleProc

theorem pair_interchange {m : ℕ} (a p d : Fin m → ℝ) (i j : Fin m)
    (hai : 0 < a i) (haj : 0 < a j) (hr : p j / a j < p i / a i)
    (t : ℝ) (hdi : d i ≤ t) (hdj : d j ≤ t) :
    taskLoss p d i (t + a i) + taskLoss p d j (t + a i + a j) <
      taskLoss p d j (t + a j) + taskLoss p d i (t + a j + a i) := by sorry

end McNaughtonSched.SingleProc
