-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_nemirovski_roos_terlaky
-- name    : ModernConvex.Relaxations.nemirovski_roos_terlaky
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:34:01.743669+00:00
-- url     : https://prove2.me/theorems/8366f9c3-bb84-4d72-bc9e-8201211039b7
-- title:
--   Proposition 4.10.6 — (Nemirovski, Roos, Terlaky) F∗ ≤ 2 ln(2 Σᵢ Rank(Bᵢ)) f∗
-- statement:
--   Consider the setting (SL.??): $n\times n$ matrices $B_1, \dots, B_m$, numbers $d_1, \dots, d_m$, the system $(S')$: $x^TB_ix \le d_i$, $i = 1, \dots, m$, and $f(x) = x^TAx$ with $A$ symmetric. Let $f^*$ be the optimal value of $(P)\ \max_x\{x^TAx : x^TB_ix \le d_i\}$, $F^*$ the optimal value of
--   $$(SDP)\qquad \max_X\{\operatorname{Tr}(AX) : \operatorname{Tr}(B_iX) \le d_i,\ i = 1,\dots,m,\ X = X^T \succeq 0\},$$
--   and $(SDD)$ the problem $\min_\lambda\{\sum_i\lambda_id_i : \sum_i\lambda_iB_i \succeq A,\ \lambda \ge 0\}$. Assume $B_i \succeq 0$, $d_i > 0$, $i = 1, \dots, m$, and $\sum_i B_i \succ 0$. Then $f^* \ge 0$, $(SDD)$ is solvable with the optimal value $F^*$, and
--   $$F^* \le 2\ln\Big(2\sum_{i=1}^m \operatorname{Rank}(B_i)\Big)\,f^*. \qquad (4.10.138)$$
--
--   Without any commutativity assumption, the semidefinite relaxation of a maximization of a quadratic form under convex quadratic constraints is tight up to a factor logarithmic in the total rank of the constraints.
--
--   **Formalization Note** $f^*$ and $F^*$ enter through "least upper bound" predicates (definition `ModernConvex.Relaxations.QuadraticSystem`); under the hypotheses both values exist. $A$ symmetric is an explicit hypothesis (the book's homogeneous quadratic form). $\ln$ is `Real.log`; its argument $2\sum_i\operatorname{Rank}(B_i)$ is at least $2n \ge 2$ whenever $n \ge 1$, because $\sum_iB_i \succ 0$. The book's exercise 4.61.3 prints the bound without the factor $2$ inside the logarithm; that printed form is false (finding F2) and the statement here is the one of (4.10.138).
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 315, Proposition 4.10.6, (4.10.138) (setting (SL.??), p. 313; (SDD), p. 314)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_QuadraticSystem

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Proposition 4.10.6 (Nemirovski, Roos, Terlaky), p. 315. Consider (SL.??)
(p. 313): a symmetric `A`, `f(x) = xᵀAx`, `f∗` the optimal value of (P) and `F∗` the optimal value
of (SDP), and assume `Bᵢ ⪰ 0`, `dᵢ > 0`, `i = 1, …, m`, and `Σᵢ Bᵢ ≻ 0`. Then `f∗ ≥ 0`, (SDD) is
solvable with the optimal value `F∗`, and `F∗ ≤ 2 ln(2 Σ_{i=1}^m Rank(Bᵢ)) f∗` (4.10.138). -/
theorem nemirovski_roos_terlaky {n m : ℕ} (S : QuadraticSystem n m) (hA : S.A.IsHermitian)
    (hB : ∀ i, (S.B i).PosSemidef) (hd : ∀ i, 0 < S.d i) (hsum : (∑ i, S.B i).PosDef)
    (fstar Fstar : ℝ) (hf : S.IsPValue fstar) (hF : S.IsSDPValue Fstar) :
    0 ≤ fstar ∧ S.SDDSolvableWithValue Fstar ∧
      Fstar ≤ 2 * Real.log (2 * ∑ i, ((S.B i).rank : ℝ)) * fstar := by sorry

end ModernConvex.Relaxations
