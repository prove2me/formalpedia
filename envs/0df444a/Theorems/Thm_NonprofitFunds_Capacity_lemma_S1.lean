-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S1
-- name    : NonprofitFunds.Capacity.lemma_S1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:57.637868+00:00
-- url     : https://prove2.me/theorems/5a4f46e6-3acd-433f-9e73-671341ed196a
-- title:
--   Lemma S.1, p. S5 (PDF 34) — second-period optimum: V2 = min(ψ2, k2, (r+1)B̂2)
-- statement:
--   Consider the second (last) period with budget $B_2$, needs $\psi_2\ge 0$ and capacity $k_2\ge 0$, with $B_2\ge m(k_2)$. Write $\hat B_2=B_2-m(k_2)$ for the net budget and
--   $$z=\min\Big(\frac{\psi_2}{r+1},\frac{k_2}{r+1}\Big).$$
--   The second-period problem maximizes $(r+1)p_2$ over $p_2,a_2,f_2\ge 0$ with $p_2+a_2+m(k_2)+f_2\le B_2$ and $(r+1)p_2\le\min(k_2,\psi_2)$. Then:
--   1. the maximum is attained, and
--   $$V_2(B_2,\psi_2,k_2)=\min\big(\psi_2,\ k_2,\ (r+1)\hat B_2\big);$$
--   2. if $\hat B_2\le z$, a feasible allocation is optimal exactly when $p_2=\hat B_2$, $a_2=0$ and $f_2=0$;
--   3. if $\hat B_2>z$, a feasible allocation is optimal exactly when $p_2=z$.
--
--   This closed form for the last period is what turns the dynamic program (1) into the single-period problem (2) of Lemma 1.
--
--   **Formalization Note.** The page's part (b) reads "any $a_2+f_2=\hat B_2-p_2$"; since constraint (1a) is an inequality, any $a_2,f_2\ge 0$ with $a_2+f_2\le\hat B_2-z$ is also optimal, and the statement says so by characterizing optimality through $p_2$ alone. Constraint (1e) at $t=2$ is not part of the second-period problem (see the model file).
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), p. S5 (PDF 34), Lemma S.1

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.1, p. S5: the second-period problem. With `B̂2 = B2 − m(k2)` and
`z = min(ψ2/(r + 1), k2/(r + 1))`: the optimal reward is `V2 = min(ψ2, k2, (r + 1) B̂2)`
(attained); if `B̂2 ≤ z` an allocation is optimal iff `p2 = B̂2, a2 = f2 = 0`; if `B̂2 > z`
an allocation is optimal iff `p2 = z`. -/
theorem lemma_S1 (P : Params) (hP : P.Standing) (B2 psi2 k2 : ℝ) (hpsi2 : 0 ≤ psi2)
    (hk2 : 0 ≤ k2) (hB2 : P.m k2 ≤ B2) :
    IsGreatest (P.V2Set B2 psi2 k2) (min psi2 (min k2 ((P.r + 1) * (B2 - P.m k2)))) ∧
    P.V2 B2 psi2 k2 = min psi2 (min k2 ((P.r + 1) * (B2 - P.m k2))) ∧
    (B2 - P.m k2 ≤ min (psi2 / (P.r + 1)) (k2 / (P.r + 1)) →
      ∀ p a f, P.Feasible2nd B2 psi2 k2 p a f →
        ((P.r + 1) * p = min psi2 (min k2 ((P.r + 1) * (B2 - P.m k2))) ↔
          p = B2 - P.m k2 ∧ a = 0 ∧ f = 0)) ∧
    (min (psi2 / (P.r + 1)) (k2 / (P.r + 1)) < B2 - P.m k2 →
      ∀ p a f, P.Feasible2nd B2 psi2 k2 p a f →
        ((P.r + 1) * p = min psi2 (min k2 ((P.r + 1) * (B2 - P.m k2))) ↔
          p = min (psi2 / (P.r + 1)) (k2 / (P.r + 1)))) := by sorry

end NonprofitFunds.Capacity
