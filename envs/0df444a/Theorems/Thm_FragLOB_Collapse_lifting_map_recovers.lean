-- Prove2me | Theorems.Thm_FragLOB_Collapse_lifting_map_recovers
-- name    : FragLOB.Collapse.lifting_map_recovers
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:20:43.260705+00:00
-- url     : https://prove2.me/theorems/085881ce-0b86-4a07-85fb-0a0c177ea091
-- title:
--   §3.2, p. 1331 — in equilibrium, Q* is inferred from the workload W* through the lifting map (15)
-- statement:
--   Let $(\pi^*, Q^*)$ be an equilibrium of the fragmented limit order book market (Definition 1) and let $W^* = \beta^\top Q^*$ be its workload. Then the queue length vector is recovered from the workload through the lifting map (15):
--
--   $$Q^*_i = \Big(\lambda_i + \Lambda\int_0^\infty \pi^*_i(\gamma)\,dF(\gamma)\Big)\frac{W^*}{\mu\beta_i}, \qquad i = 1,\dots,N.$$
--
--   This is the sense in which the $N$-dimensional equilibrium state collapses to one dimension: given the routing decisions, the workload alone determines every queue length. The paper repeats it after the proof of Theorem 1 (p. 1332): "$Q^*$ is determined as a function of workload $W^*$ through the lifting map (15)".
--
--   **Formalization Note.** Equilibrium includes $\beta^\top Q^* > 0$ (without which (4) is undefined) and individual rationality for $F$-almost every type; only the flow balance (11) and the positivity of the workload enter this statement. $F$ is a probability distribution on $[0,\infty)$.
-- source:
--   Maglaras, Moallemi & Zheng, Operations Research 69(4):1324–1348 (2021), p. 1331, §3.2 (paragraph before Theorem 1); also p. 1332 after the proof of Theorem 1

import Mathlib
import Definitions.Def_FragLOB_Collapse_Model

open MeasureTheory

namespace FragLOB.Collapse

theorem lifting_map_recovers {N : ℕ} (M : Market N) (hM : M.Standing) (F : Measure ℝ)
    [IsProbabilityMeasure F] (hF : F (Set.Iio 0) = 0) (pi : ℝ → Fin (N + 1) → ℝ)
    (Q : Fin N → ℝ) (hEq : IsEquilibrium M F pi Q) :
    Q = lift M F pi (workload M Q) := by sorry

end FragLOB.Collapse
