-- Prove2me | Theorems.Thm_HeathcoteUnbounded_psi_position_expectation_infinite
-- name    : HeathcoteUnbounded.psi_position_expectation_infinite
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-13T14:36:33.160975+00:00
-- url     : https://prove2.me/theorems/d12ca859-62ba-4f7c-b86d-ed8c62f6c612
-- title:
--   The position expectation $\int x|\psi(x)|^2dx$ of $\psi$ is infinite
-- statement:
--   For the wave function $\psi$ of eq. (4), the would-be expectation value of position
--
--   $$\mu_\psi=\langle\psi,Q\psi\rangle=\int_{\mathbb R}x\,|\psi(x)|^2\,dx$$
--
--   is infinite: $\int_{\mathbb R}|x|\,|\psi(x)|^2\,dx=\int_1^\infty x^{-1}\,dx=\infty$. The source: "This expectation value, or mean value, is undefined precisely because it is infinite."
--
--   **Formalization Note** Stated with $|x|$ as a Lebesgue integral in $[0,\infty]$; since $\psi$ vanishes for $x<1$ this equals $\int x|\psi|^2$.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 9

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi

open MeasureTheory

namespace HeathcoteUnbounded

theorem psi_position_expectation_infinite : ∫⁻ x : ℝ, ‖x‖ₑ * ‖psi x‖ₑ ^ 2 = ⊤ := by sorry

end HeathcoteUnbounded
