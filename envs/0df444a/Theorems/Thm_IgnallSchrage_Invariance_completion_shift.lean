-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_completion_shift
-- name    : IgnallSchrage.Invariance.completion_shift
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:30:51.902155+00:00
-- url     : https://prove2.me/theorems/6423c8cf-c42d-4926-8efc-408972015b36
-- title:
--   p. 411 — adding $G$ to all processing times delays the $r$-th completion on machine $M$ by $G(r+M-1)$
-- statement:
--   Let $\sigma$ be a full sequence of $n$ jobs with nonnegative processing times, and let $G>0$. Add $G$ to every processing time. For every $1\le r\le n$, consider the completion times of the job in position $r$ (1-based) in the as-soon-as-possible schedule of $\sigma$. On three machines,
--   $$
--   \tilde T_A(r)=T_A(r)+rG,\qquad \tilde T_B(r)=T_B(r)+(r+1)G,\qquad \tilde T_C(r)=T_C(r)+(r+2)G,
--   $$
--   where $(T_A,T_B,T_C)(r)$ is Johnson's completion triple after $r$ positions. On two machines the completion time on machine $B$ of the job in position $r$ rises by $(r+1)G$.
--
--   This is the paper's "increase in the completion time of the $r$th job in the schedule by $G(r+M-1)$" on machine $M$, for $M=1,2,3$ of three machines and $M=2$ of two. Every later shift statement rests on it.
--
--   **Formalization Note** The paper states no sign condition. The identity needs nonnegative processing times: with $a_i<0$ the first job's start on machine $B$, $\max(0,a_i+G)$, is not $\max(0,a_i)+G$. Processing times are durations, so nonnegativity is the paper's standing convention. The paper's hypothesis $G>0$ is kept.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, proof of the THEOREM (completion time of the rth job increased by G(r+M−1))

import Mathlib
import Definitions.Def_JohnsonFlowShop_ThreeStage_asapSchedule
import Definitions.Def_JohnsonFlowShop_TwoStage_asapStart2

namespace IgnallSchrage.Invariance

/-- p. 411: adding a constant `G` to all processing times (all nonnegative) raises the completion time of the
`r`-th job of a permutation schedule on machine `M` by `G (r + M - 1)`. Three machines: after
`r ≥ 1` positions, machines A, B, C finish `r G`, `(r + 1) G`, `(r + 2) G` later; two machines:
machine B finishes `(r + 1) G` later. -/
theorem completion_shift {n : ℕ} (a b c : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i) (G : ℝ) (hG : 0 < G)
    (σ : Equiv.Perm (Fin n)) (r : ℕ) (hr1 : 1 ≤ r) (hrn : r ≤ n) :
    JohnsonFlowShop.ThreeStage.asapDone (fun i => a i + G) (fun i => b i + G)
        (fun i => c i + G) σ r =
      ((JohnsonFlowShop.ThreeStage.asapDone a b c σ r).1 + r * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.1 + (r + 1) * G,
       (JohnsonFlowShop.ThreeStage.asapDone a b c σ r).2.2 + (r + 2) * G) ∧
    JohnsonFlowShop.TwoStage.asapC2 (fun i => a i + G) (fun i => b i + G) σ r =
      JohnsonFlowShop.TwoStage.asapC2 a b σ r + (r + 1) * G := by sorry

end IgnallSchrage.Invariance
