-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_threeMachine_shift
-- name    : IgnallSchrage.Invariance.threeMachine_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:34:38.98991+00:00
-- url     : https://prove2.me/theorems/8eb8d09c-ecc9-4764-9505-fb1a52496525
-- title:
--   p. 411 — on three machines, adding $G$ raises every makespan and every non-root $LB(J_r)$ by $G(n+2)$
-- statement:
--   Consider $n\ge1$ jobs on three machines with nonnegative processing times, and let $G>0$. Add $G$ to every processing time. Then
--
--   1. the makespan of every full sequence $\sigma$ increases by $G(n+2)$;
--   2. the lower bound of p. 401 of every node $J_r$ ($r$ distinct jobs) with $1\le r\le n-1$ increases by $G(n+2)$:
--   $$
--   \widetilde{LB}(J_r)=LB(J_r)+G(n+2).
--   $$
--
--   Together with the two-machine shift, this is the paper's "the same arguments hold for the 3-machine case".
--
--   **Formalization Note** The page says "all lower bounds". At the root $r=0$ the claim is false, because $\mathrm{TIMEB}(\emptyset)=0$ does not move. For example $n=3$, $a=(3,2,5)$, $b=(2,8,8)$, $c=(8,7,4)$, $G=1$ gives $LB(\emptyset)=22$ before the shift and $26$ after, not $27$. The root is never compared with another node, so the statement is restricted to $1\le r\le n-1$. Nonnegative processing times are assumed, as for the completion-time shift.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (3-machine lower bounds and makespans increased by G(n+2))

import Mathlib
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine

namespace IgnallSchrage.Invariance

/-- p. 411: on three machines, adding `G` to all processing times (all nonnegative) raises the makespan of every
sequence by `G (n + 2)` (for `n ≥ 1`), and the lower bound `LB(J_r)` of every node with
`1 ≤ r ≤ n - 1` by `G (n + 2)`. The page says "all lower bounds"; at the root `r = 0` the
claim is false (`TIMEB(∅) = 0` rises by `0`, not `G`), so the root is excluded. -/
theorem threeMachine_shift {n : ℕ} (hn : 1 ≤ n) (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      IgnallSchrage.Makespan.makespan (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) σ =
        IgnallSchrage.Makespan.makespan a b c σ + G * (n + 2)) ∧
    (∀ J : List (Fin n), J.Nodup → 1 ≤ J.length → J.length + 1 ≤ n →
      lowerBound3 (fun i => a i + G) (fun i => b i + G) (fun i => c i + G) J =
        lowerBound3 a b c J + G * (n + 2)) := by sorry

end IgnallSchrage.Invariance
