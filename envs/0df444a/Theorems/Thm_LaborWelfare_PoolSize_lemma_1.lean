-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_lemma_1
-- name    : LaborWelfare.PoolSize.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:04.391988+00:00
-- url     : https://prove2.me/theorems/f56cb15a-fd64-4288-8039-fb37755aa6f2
-- title:
--   Lemma 1, pp. 9–10 — a unique optimum with D*, S* > 0 exists iff β > 1 or (β = 1 and N > 8h/(v̄²E[1/a]))
-- statement:
--   In the base model ($h>0$) with labor pool size $N>0$, the platform's problem (7) has a unique optimal outcome $(p^*,w^*,D^*,S^*)$ with $D^*>0$ and $S^*>0$ if and only if
--   $$\beta>1\quad\text{or}\quad\Big(\beta=1\ \text{and}\ N>\frac{8h}{\bar v^2E[1/a]}\Big).$$
--
--   The lemma identifies the regime $N>\underline N$ in which all of the paper's comparative statics in $N$ are stated.
--
--   **Formalization Note** Positivity of $D^*$ and $S^*$ is part of feasibility. $N>0$ is assumed (a population size).
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), Lemma 1, pp. 9–10 (proof p. OA3)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Lemma 1, pp. 9–10: a unique optimum with `D* > 0`, `S* > 0` exists iff `β > 1`, or `β = 1` and
`N > 8h/(v̄² E[1/a])`. -/
theorem lemma_1 (M : Model) (hM : M.Std) (hh : 0 < M.h) (N : ℝ) (hN : 0 < N) :
    (∃! o : Outcome, IsOptimal M N o) ↔
      (1 < M.beta ∨ (M.beta = 1 ∧ 8 * M.h / (M.vbar ^ 2 * Einv M) < N)) := by sorry

end LaborWelfare.PoolSize
