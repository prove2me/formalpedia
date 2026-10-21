-- Prove2me | Theorems.Thm_NashPoly_Generic_generic_nonsingular
-- name    : NashPoly.Generic.generic_nonsingular
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:06.222116+00:00
-- url     : https://prove2.me/theorems/8e2c38b0-b4bf-42fa-b8ee-b82dbb804964
-- title:
--   §3.1, p. 8 — for generic constraining polynomials of positive degrees, every tuple g_i is nonsingular
-- statement:
--   Fix positive degrees $d_{i,j}>0$ (and any multi-degrees $a_i$ for the objectives). For Lebesgue-almost every coefficient vector $c$ of the input data, every player's constraining tuple $g_i=(g_{i,1},\dots,g_{i,m_i})$, with $g_{i,j}$ a polynomial in $x_i$ of degree at most $d_{i,j}$, is nonsingular: the matrix $G_i(\xi)$ of (3.1) has full column rank
--   $$\operatorname{rank}G_i(\xi)=m_i\qquad\text{for every }\xi\in\mathbb C^{n_i}.$$
--
--   This is why the paper's standing assumption ("every constraining polynomial tuple $g_i$ is nonsingular") is called a generic assumption; it is also the first step of the proof of Theorem A.1.
--
--   **Formalization Note** The statement is posed on the full coefficient space of the NEPP (objectives included); since that space is a product and the conclusion involves only the constraint coefficients, this is equivalent to the statement on the constraint coefficients alone. The paper cites [44, Proposition 2.1] for it.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 8 (citing [44, Proposition 2.1]); used on p. 29

import Mathlib
import Definitions.Def_NashPoly_Generic_Coef
import Definitions.Def_NashPoly_Generic_ComplexKKT

namespace NashPoly.Generic

open MvPolynomial MeasureTheory

/-- §3.1, p. 8 ([44, Proposition 2.1]): for positive degrees `d_{i,j}`, for Lebesgue-almost every
coefficient vector the constraining tuple `g_i = (g_{i,1}, …, g_{i,m_i})` of every player is
nonsingular: `G_i(ξ)` has full column rank for every `ξ ∈ ℂ^{n_i}`. -/
theorem generic_nonsingular {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)), ∀ i, Nonsingular (polyG c i) := by sorry

end NashPoly.Generic
