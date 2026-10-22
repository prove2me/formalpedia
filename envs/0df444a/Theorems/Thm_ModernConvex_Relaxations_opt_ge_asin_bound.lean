-- Prove2me | Theorems.Thm_ModernConvex_Relaxations_opt_ge_asin_bound
-- name    : ModernConvex.Relaxations.opt_ge_asin_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:33:42.668134+00:00
-- url     : https://prove2.me/theorems/034e0de1-62a7-4d7a-8019-74970a65da4c
-- title:
--   Lemma 4.3.1 — OPT ≥ (2/π) Σ aᵢⱼ asin(Xᵢⱼ) for every X feasible for (4.3.18)
-- statement:
--   Let $A = [a_{ij}]$ be a symmetric $n\times n$ real matrix and let $\mathrm{OPT}$ be the optimal value of
--   $$(4.3.17)\qquad \max_x\{x^TAx : x \in S_n\},$$
--   where $S_n$ is the set of vectors with coordinates $\pm1$. Call $X$ feasible for (4.3.18) if $X = X^T \succeq 0$ and $X_{ii} = 1$, $i = 1, \dots, n$, and let $\operatorname{asin}[X]$ be the matrix with the elements $\operatorname{asin}(X_{ij})$. Then:
--
--   1. for every $X$ feasible for (4.3.18),
--   $$\mathrm{OPT} \ge \frac{2}{\pi}\sum_{i,j=1}^n a_{ij}\operatorname{asin}(X_{ij});$$
--   2. consequently, the maximum below exists and
--   $$\mathrm{OPT} \ge \frac{2}{\pi}\max\big\{\operatorname{Tr}(A\operatorname{asin}[X]) \mid X \succeq 0,\ X_{ii} = 1,\ i = 1, \dots, n\big\}. \qquad (4.3.19)$$
--
--   The lemma is the first half of the proof of Nesterov's theorem: it bounds the combinatorial optimum from below by a nonlinear function of any point of the relaxation.
--
--   **Formalization Note** $\mathrm{OPT}$ enters through the predicate "is the least upper bound of $x^TAx$ over $S_n$"; part 2 asserts the existence of the maximum in (4.3.19) (`IsGreatest`) together with the bound. Symmetry of $A$ is the hypothesis `A.IsHermitian`.
-- source:
--   Ben-Tal & Nemirovski, Lectures on Modern Convex Optimization, SIAM 2001, p. 174, Lemma 4.3.1, (4.3.19) (problems (4.3.17), (4.3.18), p. 173)

import Mathlib
import Definitions.Def_ModernConvex_Relaxations_SignRelaxations

open Matrix

namespace ModernConvex.Relaxations

/-- Ben-Tal–Nemirovski, Lemma 4.3.1, p. 174: for a symmetric `A`, if `X` is feasible for
(4.3.18) then the optimal value `OPT` of (4.3.17) satisfies
`OPT ≥ (2/π) Σ_{i,j=1}^n aᵢⱼ asin(Xᵢⱼ)`; consequently the maximum in (4.3.19),
`max {Tr(A asin[X]) | X ⪰ 0, Xᵢᵢ = 1, i = 1, …, n}`, exists and
`OPT ≥ (2/π) · max {Tr(A asin[X]) | X ⪰ 0, Xᵢᵢ = 1}` (4.3.19). -/
theorem opt_ge_asin_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsHermitian)
    (OPT : ℝ) (hOPT : IsSignQPValue A OPT) :
    (∀ X : Matrix (Fin n) (Fin n) ℝ, IsUnitDiagPSD X →
        2 / Real.pi * ∑ i, ∑ j, A i j * Real.arcsin (X i j) ≤ OPT) ∧
      ∃ M : ℝ, IsGreatest ((fun X => (A * asinMatrix X).trace) '' {X | IsUnitDiagPSD X}) M ∧
        2 / Real.pi * M ≤ OPT := by sorry

end ModernConvex.Relaxations
