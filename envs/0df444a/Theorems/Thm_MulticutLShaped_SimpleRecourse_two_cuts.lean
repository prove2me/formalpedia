-- Prove2me | Theorems.Thm_MulticutLShaped_SimpleRecourse_two_cuts
-- name    : MulticutLShaped.SimpleRecourse.two_cuts
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:03:08.111871+00:00
-- url     : https://prove2.me/theorems/c122b7dc-495e-442d-bd45-277a336eb62c
-- title:
--   Section 5, Eqs. (22)-(23) — only two cuts per $\theta_{ij}$ in simple recourse
-- statement:
--   Let $q^+,q^-,h,\chi\in\mathbb R$ with $q^++q^-\ge 0$, and let
--   $$
--   \psi=\min\{q^+y^+ + q^-y^- \mid y^+-y^-=h-\chi,\ y^+\ge 0,\ y^-\ge 0\}
--   $$
--   be the one-row simple recourse problem (20). Then:
--
--   1. the minimum is attained, and its value is
--   $$
--   \psi=\max\{q^-(\chi-h),\ q^+(h-\chi)\};
--   $$
--   2. for every probability weight $p\ge 0$,
--   $$
--   p\,\psi=\max\{p\,q^-(\chi-h),\ p\,q^+(h-\chi)\}.
--   $$
--
--   With $p=p_{ij}$ and $(q^+,q^-,h)=\xi_{ij}$, this is the statement that, in the multicut approximation $\sum_{i,j}\theta_{ij}$ of $\Psi$, the only optimality cuts for $\theta_{ij}\ge p_{ij}\psi_i(\chi_i,\xi_{ij})$ are (22) $\theta_{ij}\ge p_{ij}q^-_{ij}(\chi_i-h_{ij})$ and (23) $\theta_{ij}\ge p_{ij}q^+_{ij}(h_{ij}-\chi_i)$. It is the step that turns the simple recourse problem into the LP (25).
--
--   **Formalization Note.** The hypothesis $q^++q^-\ge 0$ is the paper's implicit standing assumption; without it the LP is unbounded below. $\psi$ is the `EReal` infimum of the LP's objective values, so the theorem asserts that this infimum is finite and equals the closed form.
-- source:
--   Birge and Louveaux, A multicut algorithm for two-stage stochastic linear programs, Eur. J. Oper. Res. 34 (1988), p. 389, Section 5, Eqs. (22), (23)

import Mathlib
import Definitions.Def_MulticutLShaped_SimpleRecourse_Model

namespace MulticutLShaped.SimpleRecourse

/-- (22)–(23), p. 389: when `q⁺ + q⁻ ≥ 0`, the one-row LP (20) attains its minimum, its value is
`max(q⁻(χ − h), q⁺(h − χ))`, and for every probability weight `p ≥ 0`,
`p ψ = max(p q⁻(χ − h), p q⁺(h − χ))`, so only the two cuts (22), (23) arise for `θ_ij`. -/
theorem two_cuts (qp qm h χ : ℝ) (hq : 0 ≤ qp + qm) :
    (∃ yp ym : ℝ, 0 ≤ yp ∧ 0 ≤ ym ∧ yp - ym = h - χ ∧
      qp * yp + qm * ym = max (qm * (χ - h)) (qp * (h - χ))) ∧
    psiVal qp qm h χ = ((max (qm * (χ - h)) (qp * (h - χ)) : ℝ) : EReal) ∧
    ∀ p : ℝ, 0 ≤ p →
      (p : EReal) * psiVal qp qm h χ = ((max (p * qm * (χ - h)) (p * qp * (h - χ)) : ℝ) : EReal) := by sorry

end MulticutLShaped.SimpleRecourse
