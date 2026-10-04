-- Prove2me | Theorems.Thm_LodhaMoore_phi_y_and_Phi_a_b_c
-- name    : LodhaMoore.phi_y_and_Phi_a_b_c
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-03T06:28:54.505984+00:00
-- url     : https://prove2.me/theorems/be61885b-d822-4c86-9d30-772d7771d4d7
-- title:
--   Proposition 3.1 — φ(ξ.y) = 2φ(ξ), and Φ carries x, x₁, y₁₀ to a, b, c
-- statement:
--   For every infinite binary sequence $\xi$: $\phi(\xi.y) = 2\phi(\xi)$, $a(\Phi(\xi)) = \Phi(\xi.x)$, $b(\Phi(\xi)) = \Phi(\xi.x_1)$ and $c(\Phi(\xi)) = \Phi(\xi.y_{10})$.
-- source:
--   Lodha, Y. and Moore, J. T., A nonamenable finitely presented group of piecewise projective homeomorphisms, Groups Geom. Dyn. 10 (2016) 177–200, https://doi.org/10.4171/GGD/347 (arXiv:1308.4250v3, whose page numbers are used), p. 5, Proposition 3.1

import Mathlib
import Definitions.Def_LodhaMoore

namespace LodhaMoore

theorem phi_y_and_Phi_a_b_c (ξ : Stream' Bool) :
    phi (yFun true ξ) = 2 * phi ξ ∧ a (Phi ξ) = Phi (xFun ξ) ∧ b (Phi ξ) = Phi (xSeq [true] ξ) ∧
      c (Phi ξ) = Phi (ySeq [true, false] ξ) := by
  sorry

end LodhaMoore
