-- Prove2me | Theorems.Thm_NashPoly_Generic_kkt_points_finite
-- name    : NashPoly.Generic.kkt_points_finite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:30:55.74396+00:00
-- url     : https://prove2.me/theorems/89a25290-769e-42e9-bead-f28825569dc2
-- title:
--   Theorem A.1 (last clause), pp. 10, 28 — for generic data the NEPP has finitely many KKT points
-- statement:
--   Fix positive degrees $a_{i,j}>0$ and $d_{i,j}>0$ as in Theorem A.1. For Lebesgue-almost every coefficient vector, and for every choice of equality labels $E_i\subseteq[m_i]$ (the remaining constraints being inequalities), the NEPP has finitely many real KKT points (2.5): the set of $x\in X$ for which there are $\lambda_{i,j}$ with
--   $$\sum_{j=1}^{m_i}\lambda_{i,j}\nabla_{x_i}g_{i,j}(x_i)=\nabla_{x_i}f_i(x),\qquad 0\le\lambda_{i,j}\perp g_{i,j}(x_i)\ge0\ (j\in I_i)$$
--   for all $i$ is finite.
--
--   Since every point of the set $G$ of (3.7) is a KKT point, it follows that $|G\setminus G^*|\le|G|<\infty$ for generic data, which is the hypothesis of Theorem 3.2.
--
--   **Formalization Note** The null set is independent of the labels $E_i$ (the quantifier over $E$ is inside the almost-everywhere statement), as there are finitely many choices. The paper obtains this clause from (A.1) "after the enumeration of all possibilities of active inequality constraints" (p. 28).
-- source:
--   Nie & Tang, Nash Equilibrium Problems of Polynomials, arXiv:2006.09490v2, p. 28, Theorem A.1 (last clause) and the preceding paragraph; p. 10, paragraph after Theorem 3.2

import Mathlib
import Definitions.Def_NashPoly_Generic_Coef

namespace NashPoly.Generic

open MvPolynomial MeasureTheory

/-- Theorem A.1, p. 28 (last clause) and p. 10: for positive degrees `a_{i,j}`, `d_{i,j}`, for
Lebesgue-almost every coefficient vector the NEPP has finitely many (real) KKT points (2.5), for
every choice of equality labels `E_i` (the remaining constraints being inequalities). -/
theorem kkt_points_finite {N : ℕ} (n m : Fin N → ℕ) (a : Fin N → Fin N → ℕ)
    (d : (i : Fin N) → Fin (m i) → ℕ) (ha : ∀ i j, 0 < a i j) (hd : ∀ i j, 0 < d i j) :
    ∀ᵐ c ∂(volume : Measure (Coef n m a d)), ∀ E : (i : Fin N) → Finset (Fin (m i)),
      (nepOf c E).KKTSet.Finite := by sorry

end NashPoly.Generic
