-- Prove2me | Theorems.Thm_LaborWelfare_PoolSize_lemma_12
-- name    : LaborWelfare.PoolSize.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:16.779979+00:00
-- url     : https://prove2.me/theorems/a76ef758-60ff-4889-a337-6c9d247c8b62
-- title:
--   Lemma 12, p. OA2 — D̃(S) increases in S; Π(D̃(S), S) increases on (0, S*) and decreases on (S*, ∞)
-- statement:
--   Consider the base model ($h>0$) with labor pool size $N>\underline N$, and let $(p^*,w^*,D^*,S^*)$ be an optimal outcome. Then a revenue-maximizing demand $\tilde D$ exists (for each $S>0$, $\tilde D(S)\in[0,S)$ maximizes $\Pi(\cdot,S)$ over $[0,S)$), and for every such $\tilde D$:
--
--   1. $\tilde D(S)$ is strictly increasing in $S>0$;
--   2. $S\mapsto\Pi(\tilde D(S),S)$ is strictly increasing on $(0,S^*)$ and strictly decreasing on $(S^*,\infty)$.
--
--   $$\tilde D\uparrow,\qquad \Pi(\tilde D(S),S)\ \text{unimodal with peak at } S^*.$$
--
--   This is the single-peakedness of the platform's profit in labor supply, which gives the uniqueness of the optimum and the comparative statics in $N$.
-- source:
--   Benjaafar, Ding, Kong & Taylor, Labor Welfare in On-Demand Service Platforms, SSRN 3103447 (manuscript of 2020-11-13; MSOM doi:10.1287/msom.2020.0964), Lemma 12, p. OA2 (D̃(S) defined on p. OA1)

import Mathlib
import Definitions.Def_LaborWelfare_PoolSize_Setting

namespace LaborWelfare.PoolSize

open MeasureTheory Filter Topology

/-- Lemma 12, p. OA2: `D̃(S)` exists and increases in `S`; `Π(D̃(S), S)` strictly increases on
`(0, S*)` and strictly decreases on `(S*, ∞)`. -/
theorem lemma_12 (M : Model) (hM : M.Std) (hh : 0 < M.h) (N : ℝ) (hN : Nlow M < N) (o : Outcome)
    (ho : IsOptimal M N o) :
    (∃ Dt, IsDtilde M N Dt) ∧
      ∀ Dt, IsDtilde M N Dt →
        StrictMonoOn Dt (Set.Ioi 0) ∧
        StrictMonoOn (fun S => PiDS M N (Dt S) S) (Set.Ioo 0 o.S) ∧
        StrictAntiOn (fun S => PiDS M N (Dt S) S) (Set.Ioi o.S) := by sorry

end LaborWelfare.PoolSize
