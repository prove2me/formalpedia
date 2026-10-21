-- Prove2me | Theorems.Thm_NashPoly_Generic_theorem_A_1
-- name    : NashPoly.Generic.theorem_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:09.273008+00:00
-- url     : https://prove2.me/theorems/8a548be9-dcd0-444d-b806-8f908bc907c7
-- title:
--   Theorem A.1, p. 28 — for generic data the KKT system (A.1) has finitely many complex solutions
-- statement:
--   Fix positive degrees $a_{i,j}>0$ ($i,j\in[N]$) and $d_{i,j}>0$ ($i\in[N]$, $j\in[m_i]$). For Lebesgue-almost every coefficient vector, where $f_i$ is a polynomial in $x$ of degree at most $a_{i,j}$ in each block $x_j$ and $g_{i,j}$ is a polynomial in $x_i$ of degree at most $d_{i,j}$, the KKT system
--   $$\sum_{j=1}^{m_i}\lambda_{i,j}\nabla_{x_i}g_{i,j}(x_i)=\nabla_{x_i}f_i(x)\quad(i\in[N]),\qquad g_{i,j}(x_i)=0\quad(i\in[N],\ j\in[m_i])\tag{A.1}$$
--   has finitely many complex solutions $(x,\lambda)\in\mathbb C^n\times\prod_i\mathbb C^{m_i}$.
--
--   This is the algebraic core of the generic finiteness of KKT points: after fixing which inequality constraints are active, the KKT conditions of a NEPP reduce to a system of the form (A.1).
--
--   **Formalization Note** The coefficients are real (the measure is Lebesgue measure on the real coefficient space) and the solutions are complex. The statement is about pairs $(x,\lambda)$, which is stronger than finiteness of the $x$-projection. The sizes $m_i$ are arbitrary (including $m_i>n_i$, where generically there are no solutions), so the theorem can be applied to any sub-tuple of constraints. The paper's "$a_{i,j}>0,\ j\in[m_i]$" is read with $j\in[N]$ for $a$, since $a_{i,j}$ is the degree of $f_i$ in $x_j$.
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 28, Theorem A.1 and (A.1); proof pp. 28–30

import Mathlib
import Definitions.Def_NashPoly_Generic_Coef
import Definitions.Def_NashPoly_Generic_ComplexKKT

namespace NashPoly.Generic

open MvPolynomial MeasureTheory

/-- Theorem A.1, p. 28 (first clause): for positive degrees `a_{i,j}` (degree of `f_i` in `x_j`)
and `d_{i,j}` (degree of `g_{i,j}`), for Lebesgue-almost every coefficient vector the KKT system
(A.1) of the equality-constrained NEP has finitely many complex solutions `(x, λ)`. -/
theorem theorem_A_1 {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)), (A1Sol (polyF c) (polyG c)).Finite := by sorry

end NashPoly.Generic
