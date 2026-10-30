-- Prove2me | Theorems.Thm_NonRandomChoice_Assort_q0_mono_concave
-- name    : NonRandomChoice.Assort.q0_mono_concave
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T17:34:33.699159+00:00
-- url     : https://prove2.me/theorems/b2a6695f-ccb1-47a4-a18c-909a2504be95
-- title:
--   Proof of Theorem 5, p. 29 — q_0 is increasing and concave in q_{i′}
-- statement:
--   Let $\Lambda>0$ and, for $0<y<1$, let
--   $$h_\Lambda(y)=\frac{\Lambda(1-y)}{-\log y}.$$
--   In the choice model with a deterministic product $i'$ (normalized so that $a_0=1$), if $i'$ is offered then $q_{i'}=e^{-x}$ and $q_0=\Lambda(1-e^{-x})/x$ with $x=\Lambda\sum_{j\in S^+/\{i'\}}a_j>0$, so that $q_0=h_\Lambda(q_{i'})$. The claim is that $h_\Lambda$ is increasing and concave on the open interval $(0,1)$:
--   $$\frac{\partial q_0}{\partial q_{i'}}\ge0\qquad\text{and}\qquad\frac{\partial^2 q_0}{\partial q_{i'}^2}\le0\qquad\text{for }0<q_{i'}<1 .$$
--
--   This is the analytic step of the proof of Theorem 5: it is inverted in the next milestone to show that $q_{i'}$ is a convex function of $q_0$.
--
--   **Formalization Note** The statement is `MonotoneOn` and `ConcaveOn` on `Set.Ioo 0 1`. The page states the second-derivative bound for $0<q_{i'}\le1$; at $q_{i'}=1$ the formula is $0/0$, and $q_{i'}=e^{-x}<1$ in the model, so the open interval is used. With a general $a_0$, $q_0=h_{a_0\Lambda}(q_{i'})$, which is the same statement with $\Lambda$ replaced by $a_0\Lambda>0$.
-- source:
--   Wang, What Is the Impact of Non-Randomness on Random Choice Models?, SSRN 3579781 (PDF sha256 93af6c3d…), p. 29, proof of Theorem 5

import Mathlib
import Definitions.Def_NonRandomChoice_Assort_Model

namespace NonRandomChoice.Assort

theorem q0_mono_concave (Λ : ℝ) (hΛ : 0 < Λ) :
    MonotoneOn (qZeroOfQip Λ) (Set.Ioo 0 1) ∧ ConcaveOn ℝ (Set.Ioo 0 1) (qZeroOfQip Λ) := by sorry

end NonRandomChoice.Assort
