-- Prove2me | Theorems.Thm_LindgrenPriceDynamics_hamiltonian_minimizer_iff
-- name    : LindgrenPriceDynamics.hamiltonian_minimizer_iff
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-30T18:06:10.28085+00:00
-- url     : https://prove2.me/theorems/c4084ad6-e22c-4f4a-b312-d302cc9aa0e3
-- title:
--   Optimal control of the Hamiltonian: $mv_i=-\partial J/\partial p_i$
-- statement:
--   Let $m>0$, $E\in\mathbb R$ and $g\in\mathbb R^l$ (standing for the price gradient $\nabla J$ of the value function), and consider the Hamiltonian of eq. (8) as a function of the control $v\in\mathbb R^l$:
--   $$H(v)=\tfrac12 m\langle v,v\rangle+E+\langle g,v\rangle .$$
--   Then $v$ is a global minimizer of $H$ if and only if
--
--   $$m\,v_i=-g_i\qquad\text{for every commodity } i .$$
--
--   This is the optimal price-adjustment policy (9): prices move along the negative gradient of the value function.
-- source:
--   J. Lindgren, General Equilibrium with Price Adjustments — A Dynamic Programming Approach, Analytics 2022, 1, 27–34, https://doi.org/10.3390/analytics1010003, p. 30, eqs. (8)–(9)

import Mathlib
import Definitions.Def_LindgrenPriceDynamics

namespace LindgrenPriceDynamics

/-- Eq. (9): for `m > 0` the Hamiltonian (8) is minimized over the control `v`
exactly when `m v_i = -∂J/∂p_i` for every commodity `i`. -/
theorem hamiltonian_minimizer_iff {l : ℕ} (m : ℝ) (hm : 0 < m) (E : ℝ) (g v : Fin l → ℝ) :
    IsMinOn (hamiltonian m E g) Set.univ v ↔ ∀ i, m * v i = -g i := by sorry

end LindgrenPriceDynamics
