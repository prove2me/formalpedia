-- Prove2me | Theorems.Thm_HeathcoteUnbounded_psi_not_mem_positionDomain
-- name    : HeathcoteUnbounded.psi_not_mem_positionDomain
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:35:25.517734+00:00
-- url     : https://prove2.me/theorems/ef1f87e4-9407-40d9-946d-245e4c01d7ad
-- title:
--   $x\psi(x)$ is not square-integrable: $\psi\notin D(Q)$
-- statement:
--   For the wave function $\psi$ of eq. (4),
--
--   $$\int_{\mathbb R}x^2\,|\psi(x)|^2\,dx=\int_1^\infty 1\,dx=\infty .$$
--
--   Thus $Q\psi=x\psi(x)$ is not in $L^2(\mathbb R)$ and $\psi$ is not in the domain $D(Q)$ of the position operator.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 5

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi

open MeasureTheory

namespace HeathcoteUnbounded

theorem psi_not_mem_positionDomain : ∫⁻ x : ℝ, ‖x‖ₑ ^ 2 * ‖psi x‖ₑ ^ 2 = ⊤ := by sorry

end HeathcoteUnbounded
