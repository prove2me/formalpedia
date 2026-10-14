-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_eq_259_261
-- name    : InfoRelaxTS.Gap.eq_259_261
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:16.939535+00:00
-- url     : https://prove2.me/theorems/eef99245-2a92-41ee-ace7-955cf16d807f
-- title:
--   (259)–(261), §D.4.4, p. 72 — Σ_t √(L/(ν+N_{t−1}(A_t))) ≤ K√L/√ν + 2√L Σ_a √N_T(a) and Σ_a √N_T(a) ≤ √(KT)
-- statement:
--   Let $L\ge0$, $\nu>0$, and let $a_{1:T}\in\mathcal A^T$ be any action sequence over $K$ arms. Write $N_{t-1}(a)$ for the number of pulls of arm $a$ before time $t$ and $N_T(a)$ for its total number of pulls. Then
--   $$\sum_{t=1}^T\sqrt{\frac{L}{\nu+N_{t-1}(a_t)}}\le\frac{K\sqrt L}{\sqrt\nu}+2\sqrt L\sum_{a\in\mathcal A}\sqrt{N_T(a)}$$
--   and, by the Cauchy–Schwarz inequality,
--   $$\sum_{a\in\mathcal A}\sqrt{N_T(a)}\le\sqrt{KT}.$$
--
--   In the TS analysis these bounds turn the sum of per-step confidence widths into the $K/\sqrt\nu+2\sqrt{KT}$ factor of (60).
--
--   **Formalization Note** The paper applies the chain to the realized actions $A^\pi_{1:T}$ of a policy; the statement here holds for every action sequence, which covers every realization. The middle equality of (259) is an inequality when some arm is never pulled; the chain still holds.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 72, §D.4.4, (259)–(261)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

namespace InfoRelaxTS.Gap

theorem eq_259_261 {K : ℕ} (T : ℕ) (L ν : ℝ) (hL : 0 ≤ L) (hν : 0 < ν) (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (L / (ν + pullsBefore s t (s t))) ≤
        (K : ℝ) * Real.sqrt L / Real.sqrt ν + 2 * Real.sqrt L * ∑ a, Real.sqrt (pullCount s a) ∧
      ∑ a, Real.sqrt (pullCount s a) ≤ Real.sqrt ((K : ℝ) * T) := by sorry

end InfoRelaxTS.Gap
