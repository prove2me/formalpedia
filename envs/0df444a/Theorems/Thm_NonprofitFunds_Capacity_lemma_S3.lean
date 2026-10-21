-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S3
-- name    : NonprofitFunds.Capacity.lemma_S3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:00.218996+00:00
-- url     : https://prove2.me/theorems/dedb3e34-05d7-4975-8fe8-d5df87e097ff
-- title:
--   Lemma S.3, p. S6 (PDF 35) — J_nb is concave: increasing, or maximized at its unique first-order point
-- statement:
--   Fix the data and an admissible capacity $k_1$, and let
--   $$J_{nb}(p_1)=(r+1)p_1+\mathbb E_\Psi\Big[\min\big(\Psi,(r+1)\hat B_2(p_1,0)\big)\Big],\qquad p_1\in[0,\hat B_1],$$
--   the objective of problem (2) when nothing is spent on discretionary administration ($a_1=0$, $f_1=\hat B_1-p_1$). Then $J_{nb}$ is concave on $[0,\hat B_1]$, and
--   1. either $J_{nb}$ is nondecreasing on $[0,\hat B_1]$,
--   2. or there is exactly one $p_1\in(0,\hat B_1)$ at which $J_{nb}'(p_1)=0$, and this point maximizes $J_{nb}$ on $[0,\hat B_1]$.
--
--   The maximizer $\tilde p_{nb}$ of $J_{nb}$ is the unconstrained candidate for program spending in Lemma S.4.
--
--   **Formalization Note.** The first-order condition is stated as `HasDerivAt J_nb 0 p`, so a point where $J_{nb}$ is not differentiable never counts as a solution. The domain of $J_{nb}$ is taken to be $[0,\hat B_1]$ (program spending is nonnegative and the fundraising spending $\hat B_1-p_1$ is nonnegative).
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), p. S6 (PDF 35), Lemma S.3 and its proof; J_nb is (3), p. 16 (PDF 16)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.3, p. S6: `J_nb` is concave in `p1` on `[0, B̂1]`, and either it is increasing there,
or there is a unique interior first-order point, and it maximizes `J_nb` on `[0, B̂1]`. -/
theorem lemma_S3 (P : Params) (hP : P.Standing) (k1 : ℝ) (hk1 : P.Admissible k1) :
    ConcaveOn ℝ (Set.Icc 0 (P.Bhat1 k1)) (P.Jnb k1) ∧
    (MonotoneOn (P.Jnb k1) (Set.Icc 0 (P.Bhat1 k1)) ∨
      ∃ p ∈ Set.Ioo 0 (P.Bhat1 k1), HasDerivAt (P.Jnb k1) 0 p ∧
        (∀ q ∈ Set.Ioo 0 (P.Bhat1 k1), HasDerivAt (P.Jnb k1) 0 q → q = p) ∧
        IsMaxOn (P.Jnb k1) (Set.Icc 0 (P.Bhat1 k1)) p) := by sorry

end NonprofitFunds.Capacity
