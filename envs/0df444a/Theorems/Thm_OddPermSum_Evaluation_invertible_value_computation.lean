-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_invertible_value_computation
-- name    : OddPermSum.Evaluation.invertible_value_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:23:20.869374+00:00
-- url     : https://prove2.me/theorems/4d9c09f8-ccd8-4a57-b139-eda9622d1c24
-- title:
--   Lemma 3.4 — invertible scalar evaluation
-- statement:
--   Fix a characteristic-two field $F$, an achieved exponent $2<\omega\le3$, and a supplied uniformly costed multiplication program. One finite deterministic program $E$ and constants $C>0,n_0$ exist such that, for every size $n$ and every invertible matrix $A\in F^{n\times n}$, its successful execution returns
--
--   $$\Phi(A),\qquad \operatorname{cost}_E(n,A)\le Cn^\omega\quad(n\ge\max(1,n_0)).$$
--
--   Only $A$ is input. Inverse and determinant computations must be implemented and charged internally. Correctness and termination hold at every size. The program and constants may depend on the fixed field, exponent and multiplication implementation, but never on $n$, $A$, rank or entry values.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: A invertible over the field F → IsUnit (det A); reason: over a field a unit determinant is exactly a nonzero determinant, hence exactly the source's invertibility condition
--   - encoding: deterministic O(n^ω) field operations for a fixed admissible exponent → one finite algebraic program with successful primitive-costed execution at every size, and E,C,n₀ before n,A, relative to a supplied achieved multiplier; reason: makes uniform Big-O and algebraic access explicit, counts zero tests and inversion guards, and leaves constants dependent only on the fixed field, exponent and implementation
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 8, Lemma 3.4

import Definitions.Def_OddPermSum_Evaluation_phi
import Definitions.Def_OddPermSum_Evaluation_achievedExponent

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 3.4. Only A is input: computing determinant and inverse is charged internally. -/
theorem invertible_value_computation {F : Type*} [Field F] [CharP F 2]
    (ω : ℝ) (hω : 2 < ω) (hω3 : ω ≤ 3)
    (M : AlgebraicProgram F) (Cₘ : ℝ) (nₘ : ℕ)
    (hM : MultipliesWithin M ω Cₘ nₘ) :
    ∃ (E : AlgebraicProgram F) (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
        ∃ (fuel : ℕ) (s : MachineState F),
          run E n (matrixEncoding A) fuel = some s ∧
          s.outputs = [phi A] ∧
          (max 1 n₀ ≤ n → (s.cost : ℝ) ≤ C * (n : ℝ)^ω) := by sorry

end OddPermSum.Evaluation
