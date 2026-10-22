-- Prove2me | Theorems.Thm_MatrixAnalytic_PH_integral_exp_eq_neg_inv
-- name    : MatrixAnalytic.PH.integral_exp_eq_neg_inv
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:40:48.024062+00:00
-- url     : https://prove2.me/theorems/3f4d83f4-d35b-444f-91c1-d0998bcd2b18
-- title:
--   Eq. (2.11) — $\int_0^\infty \exp(Tx)\,dx = -T^{-1}$ for a nonsingular PH rate matrix
-- statement:
--   Let $T$ be a real square matrix indexed by a finite phase set that satisfies (2.4)–(2.5): $T_{ii} < 0$, $T_{ij} \ge 0$ for $i \ne j$, and $\boldsymbol t = -T\mathbf 1 \ge 0$. Suppose $T$ is nonsingular (for such matrices this is the same as $T$ being stable). Then every entry of $x \mapsto \exp(Tx)$ is integrable on $(0, \infty)$ and
--   $$\int_0^\infty \exp(Tx)\,dx = -T^{-1}.$$
--
--   Together with Theorem 2.4.3 this identifies $-T^{-1}$ as the matrix of expected sojourn times; it is the continuous-time analogue of the fundamental matrix $(I - T)^{-1}$ of an absorbing chain, and is used for the moments (2.13).
--
--   **Formalization Note** The identity is stated entrywise, with Lebesgue integrability of each entry on $(0,\infty)$ asserted as part of the conclusion, so that the Lean integral cannot take its default value $0$ on a non-integrable function. $T^{-1}$ is Mathlib's matrix inverse, which is the genuine inverse because $\det T$ is assumed to be a unit. The book states (2.11) in Remark 2.4.5 under "$T$ stable"; for a matrix satisfying (2.4)–(2.5) the book notes that stable and nonsingular are equivalent, and the hypothesis used here is nonsingularity.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 44, Remark 2.4.5, Eq. (2.11)

import Mathlib
import Definitions.Def_MatrixAnalytic_PH_Continuous

open Matrix MeasureTheory

namespace MatrixAnalytic.PH

/-- Eq. (2.11) (Latouche–Ramaswami, p. 44, Remark 2.4.5): for a rate matrix `T` satisfying (2.4),
(2.5) that is nonsingular (equivalently stable), `∫₀^∞ exp(Tx) dx = −T⁻¹`, entrywise and with
every entry absolutely integrable on `(0, ∞)`. -/
theorem integral_exp_eq_neg_inv {ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Matrix ι ι ℝ) (hT : IsPHGenerator T) (hdet : IsUnit T.det) :
    ∀ i j : ι,
      IntegrableOn (fun x : ℝ => NormedSpace.exp (x • T) i j) (Set.Ioi 0) ∧
      ∫ x in Set.Ioi (0 : ℝ), NormedSpace.exp (x • T) i j = (-T⁻¹) i j := by sorry

end MatrixAnalytic.PH
