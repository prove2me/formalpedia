-- Prove2me | Theorems.Thm_Komlos_banaszczyk_bound
-- name    : Komlos.banaszczyk_bound
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-03T20:52:39.18599+00:00
-- url     : https://prove2.me/theorems/1846fa46-fbad-4294-8e7d-4a74466da581
-- title:
--   Banaszczyk: the Komlós bound $O(\sqrt{\log n})$
-- statement:
--   (Banaszczyk 1998.) There is a constant $C > 0$ such that any $n$ vectors of Euclidean norm at most $1$, in any dimension, admit signs with every coordinate of the signed sum at most $C\sqrt{\log(n+2)}$ in absolute value. This was the best bound toward the Komlós conjecture for nearly three decades, until the $\tilde{O}((\log n)^{1/4})$ bound of Bansal--Jiang (2025). The formal statement uses $\log(n+2)$ so the bound is positive for all $n \ge 0$; the dimension $m$ is unrestricted (coordinates whose column of entries has small norm are controlled automatically, reducing to effective dimension $O(n^2)$).
-- source:
--   Banaszczyk, Balancing vectors and Gaussian measures of n-dimensional convex bodies, Random Structures & Algorithms 12 (1998) 351-360, Theorem 1 applied to the cube, https://doi.org/10.1002/(SICI)1098-2418(199810)12:4%3C351::AID-RSA3%3E3.0.CO;2-S

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem banaszczyk_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (n + 2)) := by sorry

end Komlos
