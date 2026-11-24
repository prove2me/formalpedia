-- Prove2me | Theorems.Thm_GomoryGroup_Rel_Supplement_theorem_2
-- name    : GomoryGroup.Rel.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:21:04.130551+00:00
-- url     : https://prove2.me/theorems/bec0911d-d7c1-4dad-a00f-17b6a969ad9d
-- title:
--   THEOREM 2, p. 261 — for b ∈ K^B(l(D − 1)), the optimal x(b) has Σ_{i>m} x_i = Σ y_i ≤ D − 1
-- statement:
--   In the setting of THEOREM 1 (integer basis $B$ with $\det B\neq0$, every unit vector a column of $A=(B,N)$, all relative costs $c^*_{m+1+j}\le0$, $l=\max_{i>m}\|\alpha_i\|$, $D=|\det B|$), let $b\in\mathbb Z^m$ lie in $K^B(l(D-1))$. Then the optimal solution vector $x(b)=(B^{-1}(b-Ny),y)$ of (3) can be taken with $y$ optimal for the group problem (4), $x(b)$ integral, nonnegative and optimal for P2, and
--   $$\sum_{i=m+1}^{m+n}x_i=\sum_{i=1}^ny_i\le D-1 .$$
--
--   The bound measures how far the integer optimum lies from the lattice point $p=b-Ny^B(b)$ from which it is continued.
--
--   **Formalization Note** The statement exhibits an $x(b)$ of the form (3): $x_N=y$, so $\sum_{i>m}x_i=\sum_iy_i$. Standing hypotheses as in THEOREM 1; column $j$ of $N$ is $\alpha_{m+1+j}$.
-- source:
--   Gomory, On the relation between integer and noninteger solutions to linear programs, Proc. Natl. Acad. Sci. USA 53 (1965), p. 261, THEOREM 2

import Mathlib
import Definitions.Def_GomoryGroup_Rel_Setting

namespace GomoryGroup.Rel.Supplement

open Matrix

theorem theorem_2 {m n : ℕ} (B : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin m) (Fin n) ℤ)
    (cB : Fin m → ℝ) (cN : Fin n → ℝ) (b : Fin m → ℤ)
    (hB : B.det ≠ 0) (hI : HasUnitColumns B N) (hopt : ∀ j, reducedCost B N cB cN j ≤ 0)
    (hb : (fun i => (b i : ℝ)) ∈ reducedCone B (ell N * ((detD B : ℝ) - 1))) :
    ∃ (xB : Fin m → ℕ) (y : Fin n → ℕ), IsGroupOptimal B N cB cN b y ∧
      B *ᵥ (fun i => (xB i : ℤ)) = b - N *ᵥ (fun j => (y j : ℤ)) ∧
      IsIPOptimal B N cB cN b xB y ∧ ∑ j, y j ≤ detD B - 1 := by sorry

end GomoryGroup.Rel.Supplement
