-- Prove2me | Theorems.Thm_LinearOptimization_integer_program_weak_lagrangean_duality
-- name    : LinearOptimization.integer_program_weak_lagrangean_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-09T16:00:09.974692+00:00
-- url     : https://prove2.me/theorems/d4546e97-7dca-4450-84a7-af5b9fed9656
-- title:
--   Weak integer programming duality: $Z_D \le Z_{IP}$
-- statement:
--   **(Theorem 11.2, Weak integer programming duality — Bertsimas & Tsitsiklis, p. 495.)** In the setting of Section 11.4 (integer program (11.5): minimize $c'x$ subject to $Ax \ge b$, $Dx \ge d$, $x$ integer, with $A$, $D$, $b$, $c$, $d$ of integer entries; $X = \{x\ \text{integer} \mid Dx \ge d\}$; $Z(p) = \min_{x \in X}(c'x + p'(b - Ax))$; $Z_D = \max_{p \ge 0} Z(p)$): we have
--
--   $$Z_D \le Z_{IP}.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 11.2, p. 495

import Definitions.Def_LinearOptimization_IntegerProgram
import Definitions.Def_LinearOptimization_LagrangeanDual


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 11.2 (p. 495).** Weak Lagrangean duality for the integer
program (11.5): `Z_D ≤ Z_IP` (in `EReal`, hypothesis-free). -/

theorem LinearOptimization.integer_program_weak_lagrangean_duality {m₁ m₂ n : ℕ}
    (A : Matrix (Fin m₁) (Fin n) ℤ) (b : Fin m₁ → ℤ) (c : Fin n → ℤ)
    (D : Matrix (Fin m₂) (Fin n) ℤ) (d : Fin m₂ → ℤ) :
    lagrangeanDualValue (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))
        (fun j => (c j : ℝ))
        (lagrangeanIntegerSet (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ))) ≤
      integerProgramValue (fun j => (c j : ℝ)) (A.map ((↑) : ℤ → ℝ))
        (fun i => (b i : ℝ)) (D.map ((↑) : ℤ → ℝ)) (fun i => (d i : ℝ)) := by
  sorry
