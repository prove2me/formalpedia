-- Prove2me | Theorems.Thm_Komlos_banaszczyk_cube_bound
-- name    : Komlos.banaszczyk_cube_bound
-- status  : Open
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:23:59.985722+00:00
-- url     : https://prove2.me/theorems/9f5dd85d-203c-41f2-9245-abad0170f733
-- title:
--   Banaszczyk’s cube bound in the ambient dimension
-- statement:
--   There is a universal constant $C>0$ such that, for every $n,m\ge0$ and every family $v_1,\ldots,v_n\in\mathbb R^m$ of vectors with Euclidean norm at most one, there are signs $\varepsilon_i\in\{-1,1\}$ for which
--   $$\left|\sum_{i=1}^n\varepsilon_i v_{ij}\right|\le C\sqrt{\log(m+2)}\qquad(1\le j\le m).$$
--   The logarithm depends on the ambient dimension $m$. The constant is independent of both $m$ and $n$. Using $m+2$ makes the assertion uniform at dimensions zero and one; empty families and zero-dimensional spaces are included. This is the cube consequence of Banaszczyk’s vector-balancing theorem, and is the analytic input to the separate elementary reduction to a bound depending on the number of vectors.
-- source:
--   Banaszczyk, Balancing vectors and Gaussian measures of n-dimensional convex bodies, Random Structures & Algorithms 12 (1998), Theorem 1 applied to a scaled cube. Exact cube consequence stated on p. 3, immediately after Theorem 1.1, in Dadush–Garg–Lovett–Nikolov, Towards a Constructive Version of Banaszczyk's Vector Balancing Theorem, Theory of Computing 15(15), 2019, https://theoryofcomputing.org/articles/v015a015/v015a015.pdf . The replacement log(m) by log(m+2) absorbs the low-dimensional cases into the unspecified universal constant.

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem banaszczyk_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (m + 2)) := by sorry

end Komlos
