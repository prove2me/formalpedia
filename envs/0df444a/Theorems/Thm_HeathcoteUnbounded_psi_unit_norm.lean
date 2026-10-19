-- Prove2me | Theorems.Thm_HeathcoteUnbounded_psi_unit_norm
-- name    : HeathcoteUnbounded.psi_unit_norm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-13T14:35:02.847077+00:00
-- url     : https://prove2.me/theorems/214783da-0caa-4bb7-91b8-0d6da75c894a
-- title:
--   The wave function (4) is a normalized element of $L^2(\mathbb R)$
-- statement:
--   Let $\psi(x)=x^{-1}$ for $x\ge1$ and $\psi(x)=0$ for $x<1$ (eq. (4)). Then $\psi\in L^2(\mathbb R)$ and
--
--   $$\int_{\mathbb R}|\psi(x)|^2\,dx=\int_1^{\infty}x^{-2}\,dx=1 .$$
--
--   Hence $\psi$ is a unit vector and, by Postulate 1, represents a state.
-- source:
--   A. Heathcote, "Unbounded Operators and the Incompleteness of Quantum Mechanics", Philosophy of Science 57 (1990), 523–534, p. 5, computation following eq. (4)

import Mathlib
import Definitions.Def_HeathcoteUnbounded_Psi

open MeasureTheory

namespace HeathcoteUnbounded

theorem psi_unit_norm : MemLp psi 2 volume ∧ ∫⁻ x : ℝ, ‖psi x‖ₑ ^ 2 = 1 := by sorry

end HeathcoteUnbounded
