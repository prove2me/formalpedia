-- Prove2me | Theorems.Thm_NymanBeurling_moebius_dirichlet_abel_limit
-- name    : NymanBeurling.moebius_dirichlet_abel_limit
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:06:26.272942+00:00
-- url     : https://prove2.me/theorems/ba6f3ccb-a3be-4de1-87b4-4fce40840ec3
-- title:
--   Unconditional Abel limit of the Mobius Dirichlet series at one
-- statement:
--   As the real parameter $\varepsilon$ tends to $0$ through positive values,
--   $$\sum_{n\ge1}\frac{\mu(n)}{n^{1+\varepsilon}}\longrightarrow0.$$
--   For every positive $\varepsilon$ the series is absolutely convergent. This is an unconditional theorem. The scalar limit is useful for separating finite-coordinate convergence of damped Möbius remainder sums from the still-open uniform weighted-tail estimate. No convergence of the undamped series at $s=1$, and no uniformity in the cutoff as $\varepsilon\to0$, is asserted.
--
--   Formalization note: the series is represented by Mathlib's complex-valued `LSeries` evaluated at $1+\varepsilon$.
-- source:
--   Derived entirely from Mathlib at revision 0df444a360eaa60ab8c11dca51a86af692955474: LSeries_one_mul_Lseries_moebius and LSeries_one_eq_riemannZeta (Mathlib/NumberTheory/LSeries/Dirichlet.lean), and riemannZeta_residue_one (Mathlib/NumberTheory/LSeries/RiemannZeta.lean). These are proved unconditional dependencies. Connection: https://prove2.me/theorems/cf53c71e-758a-4724-897b-66cd8091e51b .

import Mathlib

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

theorem NymanBeurling.moebius_dirichlet_abel_limit :
    Tendsto (fun ε : ℝ =>
      LSeries (fun n => (ArithmeticFunction.moebius n : ℂ)) (1 + (ε : ℂ)))
      (𝓝[>] 0) (𝓝 0) := by sorry
