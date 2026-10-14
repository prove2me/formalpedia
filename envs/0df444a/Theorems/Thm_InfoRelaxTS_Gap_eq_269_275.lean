-- Prove2me | Theorems.Thm_InfoRelaxTS_Gap_eq_269_275
-- name    : InfoRelaxTS.Gap.eq_269_275
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:34.424024+00:00
-- url     : https://prove2.me/theorems/e3c18904-350f-4172-8fbd-054da4074097
-- title:
--   (269)–(275), §D.4.4, p. 73 — Σ_t √(1/(ν+N_{t−1}(A_t)) − 1/(ν+T)) ≤ K/√ν + 2√(KT) − (1/3)√(T/K)
-- statement:
--   Let $K\ge1$, $T\ge1$, $\nu>0$, and let $a_{1:T}\in\mathcal A^T$ be any action sequence over $K$ arms. Write $N_{t-1}(a)$ for the number of pulls of arm $a$ before time $t$. Then
--   $$\sum_{t=1}^T\sqrt{\frac1{\nu+N_{t-1}(a_t)}-\frac1{\nu+T}}\le\frac{K}{\sqrt\nu}+2\sqrt{KT}-\frac13\sqrt{\frac TK}.$$
--
--   In the IRS.FH and IRS.V-Zero analyses this bound produces the extra $-\tfrac13\sqrt{T/K}$ term of (61) and (62).
--
--   **Formalization Note** The left side of (269) prints $N^\pi_{t-1}(a)$; $N^\pi_{t-1}(A^\pi_t)$ is meant, since the sum runs over the pulled arms. The statement holds for every action sequence, covering every realization of $A^\pi_{1:T}$. The radicand is nonnegative because $N_{t-1}(a)\le T-1$, so no square root of a negative number occurs. The constant $\tfrac13$ is the printed one.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 73, §D.4.4, (269)–(275)

import Mathlib
import Definitions.Def_InfoRelaxTS_Gap_Setting

namespace InfoRelaxTS.Gap

theorem eq_269_275 {K : ℕ} [NeZero K] (T : ℕ) (hT : 1 ≤ T) (ν : ℝ) (hν : 0 < ν)
    (s : Fin T → Fin K) :
    ∑ t, Real.sqrt (1 / (ν + pullsBefore s t (s t)) - 1 / (ν + T)) ≤
      (K : ℝ) / Real.sqrt ν + 2 * Real.sqrt ((K : ℝ) * T)
        - (1 / 3) * Real.sqrt ((T : ℝ) / K) := by sorry

end InfoRelaxTS.Gap
