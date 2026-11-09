-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_evaluate_value_gradient
-- name    : OddPermSum.Evaluation.evaluate_value_gradient
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:23:50.663595+00:00
-- url     : https://prove2.me/theorems/489d5b6f-a329-4baa-b90e-26baf92f7d1d
-- title:
--   Theorem 1.1 — deterministic value and full-gradient computation
-- statement:
--   Fix any characteristic-two field $F$, including finite or infinite fields, any achieved square-matrix multiplication exponent $2<\omega\le3$, and a supplied deterministic multiplication program $M$ with uniform cost constant $C_M$ and threshold $n_M$. There exist a single finite deterministic algebraic program $E$, a constant $C>0$ and a threshold $n_0$, all chosen before $n$ and $A$, such that for every size $n$ and every matrix $A\in F^{n\times n}$ the execution terminates and returns both
--
--   $$\Phi(A)\quad\text{and}\quad G(A)_{j,i}=\left(\frac{\partial\Phi_n}{\partial x_{i,j}}\right)(A)\quad\text{for all }i,j,$$
--
--   with actual primitive cost
--
--   $$\operatorname{cost}_E(n,A)\le Cn^\omega\qquad(n\ge\max(1,n_0)).$$
--
--   Correctness and termination include sizes zero and one and every rank, also below the threshold. The output is the scalar followed by the row-major encoding of the entire transposed formal gradient. $E,C,n_0$ may depend on $F,\omega$ and the supplied multiplication implementation and its constants, never on size, entries or rank. Arithmetic and zero tests are counted from execution; determinant, inverse, rank and multiplication subroutines are not free primitives. The formal gradient is defined independently of the evaluator, and the goal assumes no evaluator or gradient oracle. There is no exponent slack or logarithmic loss.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: deterministic O(n^ω) field operations for a fixed admissible exponent → one finite algebraic program with successful primitive-costed execution at every size, and E,C,n₀ before n,A, relative to a supplied achieved multiplier; reason: makes uniform Big-O and algebraic access explicit, counts zero tests and inversion guards, and leaves constants dependent only on the fixed field, exponent and implementation
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 2, Theorem 1.1 (proof p. 12)

import Definitions.Def_OddPermSum_Evaluation_gradient
import Definitions.Def_OddPermSum_Evaluation_achievedExponent

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Theorem 1.1. One finite deterministic algebraic program returns the value and
the ENTIRE transposed formal gradient over every characteristic-two field, at every
rank and every size. The program and bound precede n and A. The supplied multiplier
is itself a primitive-costed program, not a free oracle or an evaluator hypothesis. -/
theorem evaluate_value_gradient {F : Type*} [Field F] [CharP F 2]
    (ω : ℝ) (hω : 2 < ω) (hω3 : ω ≤ 3)
    (M : AlgebraicProgram F) (Cₘ : ℝ) (nₘ : ℕ)
    (hM : MultipliesWithin M ω Cₘ nₘ) :
    ∃ (E : AlgebraicProgram F) (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
        ∃ (fuel : ℕ) (s : MachineState F),
          run E n (matrixEncoding A) fuel = some s ∧
          s.outputs = phi A :: matrixEncoding (gradient A) ∧
          (max 1 n₀ ≤ n → (s.cost : ℝ) ≤ C * (n : ℝ)^ω) := by sorry

end OddPermSum.Evaluation
