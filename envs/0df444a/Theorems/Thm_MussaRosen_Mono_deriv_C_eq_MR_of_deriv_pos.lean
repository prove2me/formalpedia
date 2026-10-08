-- Prove2me | Theorems.Thm_MussaRosen_Mono_deriv_C_eq_MR_of_deriv_pos
-- name    : MussaRosen.Mono.deriv_C_eq_MR_of_deriv_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:31:50.67028+00:00
-- url     : https://prove2.me/theorems/2dbad080-b049-437f-a137-09d012c4ca8b
-- title:
--   (17), (i) p. 311 — q(θ) = G(θ), i.e. C′(q(θ)) = MR(θ), where q̇ > 0
-- statement:
--   Under the standing hypotheses, let $q$ be an optimal assignment and let $\underline\theta\le a<b\le\bar\theta$. If at every $\theta\in(a,b)$ the assignment is differentiable with $\dot q(\theta)>0$, then marginal cost equals marginal revenue on $(a,b)$:
--   $$C'(q(\theta))=MR(\theta)\qquad(a<\theta<b).$$
--   In the paper's notation $q(\theta)=G(\theta)$ on $(a,b)$, where $G$ is defined by $C'(G(\theta))=MR(\theta)$, equation (17).
--
--   **Formalization Note** $G$ is not introduced as a function: the statement is written through $C'$, which is equivalent wherever $G(\theta)$ exists and avoids an inverse of $C'$.
-- source:
--   Mussa and Rosen, Monopoly and product quality, J. Econ. Theory 18 (1978), p. 311, §4, case (i), equation (17)

import Mathlib
import Definitions.Def_MussaRosen_Mono_Setting

open MechanismDesign.Screening Filter Topology

namespace MussaRosen.Mono

theorem deriv_C_eq_MR_of_deriv_pos {θlo θhi : ℝ} (D : TypeDistribution θlo θhi)
    (hfd : DifferentiableOn ℝ D.f (Set.Icc θlo θhi))
    (C : ℝ → ℝ) (hC0 : C 0 = 0) (hCd : Differentiable ℝ C) (hCd2 : Differentiable ℝ (deriv C))
    (hC1 : ∀ q : ℝ, 0 ≤ q → 0 < deriv C q) (hC2 : ∀ q : ℝ, 0 ≤ q → 0 < deriv (deriv C) q)
    (q : ℝ → ℝ) (hq : IsOptimal D C q)
    (a b : ℝ) (ha : θlo ≤ a) (hab : a < b) (hb : b ≤ θhi)
    (hinc : ∀ θ ∈ Set.Ioo a b, ∃ d : ℝ, 0 < d ∧ HasDerivAt q d θ) :
    ∀ θ ∈ Set.Ioo a b, deriv C (q θ) = virtualValuation D θ := by sorry

end MussaRosen.Mono
