-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S2
-- name    : NonprofitFunds.Capacity.lemma_S2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:02.629912+00:00
-- url     : https://prove2.me/theorems/0c3171f4-9926-4c14-9474-a3f0a61ac6b9
-- title:
--   Lemma S.2, p. S6 (PDF 35) — when (2f) is not binding, the optimum has a1 = 0
-- statement:
--   Fix the data and an admissible capacity $k_1$. Consider problem (2) with the additional restriction that constraint (2f) is not binding, i.e. restrict to feasible allocations with
--   $$(r+1)\hat B_2(p_1,a_1,f_1)<k_1+\delta(a_1).$$
--   If $(p_1,a_1,f_1)$ maximizes the objective of (2) over this restricted set, then $a_1=0$.
--
--   The lemma reduces the "unused capacity" case of the analysis to the one-dimensional problem (S.1) in $p_1$ alone, in which no money is spent on discretionary administration.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), p. S6 (PDF 35), Lemma S.2

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.2, p. S6: in problem (2) with the additional restriction that (2f) is not binding,
every optimal solution has `a1 = 0`. -/
theorem lemma_S2 (P : Params) (hP : P.Standing) (k1 : ℝ) (hk1 : P.Admissible k1) (p a f : ℝ)
    (hfeas : P.Feasible2 k1 p a f)
    (hslack : (P.r + 1) * P.Bhat2 k1 p a f < k1 + P.delta a)
    (hopt : ∀ p' a' f', P.Feasible2 k1 p' a' f' →
      (P.r + 1) * P.Bhat2 k1 p' a' f' < k1 + P.delta a' → P.obj2 k1 p' a' f' ≤ P.obj2 k1 p a f) :
    a = 0 := by sorry

end NonprofitFunds.Capacity
