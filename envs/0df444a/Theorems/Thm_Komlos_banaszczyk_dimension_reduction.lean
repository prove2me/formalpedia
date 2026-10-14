-- Prove2me | Theorems.Thm_Komlos_banaszczyk_dimension_reduction
-- name    : Komlos.banaszczyk_dimension_reduction
-- status  : Proved
-- author  : @Wenqian Xing
-- created : 2026-09-06T09:23:51.798569+00:00
-- url     : https://prove2.me/theorems/255f173c-9431-40f9-892f-0d5667fe0499
-- title:
--   From ambient-dimension discrepancy bounds to bounds in the number of vectors
-- statement:
--   Suppose there is a universal constant $C>0$ such that, for all $n,m\ge0$ and all vectors $v_1,\ldots,v_n\in\mathbb R^m$ with $\|v_i\|_2\le1$, some signs $\varepsilon_i\in\{-1,1\}$ satisfy
--   $$\left|\sum_i\varepsilon_i v_{ij}\right|\le C\sqrt{\log(m+2)}\qquad(1\le j\le m).$$
--   Then there is a universal constant $D>0$ such that the same class of vector families admits signs satisfying
--   $$\left|\sum_i\varepsilon_i v_{ij}\right|\le D\sqrt{\log(n+2)}\qquad(1\le j\le m).$$
--   The ambient dimension is unrestricted in both statements, and dimensions or family sizes equal to zero are included. The conclusion is conditional on the first uniform bound; this is an elementary transfer theorem, not a proof of the cube bound or the Komlós conjecture.
-- source:
--   Elementary coordinate-selection and Cauchy–Schwarz reduction between the cube bound stated on p. 3 of Dadush–Garg–Lovett–Nikolov, Towards a Constructive Version of Banaszczyk's Vector Balancing Theorem, Theory of Computing 15(15), 2019, https://theoryofcomputing.org/articles/v015a015/v015a015.pdf , and the exact mission milestone https://prove2.me/theorems/1846fa46-fbad-4294-8e7d-4a74466da581 . The explicit coordinate-selection proof is supplied with this contribution; it is not attributed verbatim to that paper.

import Mathlib
import Definitions.Def_Komlos_model

namespace Komlos

theorem banaszczyk_dimension_reduction
    (hCube : ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (m + 2))) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (v : Fin n → EuclideanSpace ℝ (Fin m)),
      (∀ i, ‖v i‖ ≤ 1) →
      ∃ ε : Fin n → ℝ, IsSignVector ε ∧
        ∀ j, |∑ i, ε i * v i j| ≤ C * Real.sqrt (Real.log (n + 2)) := by sorry

end Komlos
