-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_crossed_sum_computation
-- name    : OddPermSum.Evaluation.crossed_sum_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:23:01.442197+00:00
-- url     : https://prove2.me/theorems/3cd1b423-6354-4771-af38-0240fa04b615
-- title:
--   Lemma 3.3 — crossed sum in matrix multiplication time
-- statement:
--   Fix a characteristic-two field $F$, an achieved exponent $2<\omega\le3$, and a supplied deterministic multiplication program with a uniform $O(n^\omega)$ primitive cost bound. There exist one program $E$, $C>0$ and $n_0$, chosen before all sizes and entries, that on every invertible $A$ receives $A$ and $B=A^{-1}$ and returns
--
--   $$T(A,B)=\sum_{i<j,\ k>l}A_{i,k}B_{k,j}A_{j,l}B_{l,i},\qquad \operatorname{cost}_E\le Cn^\omega\quad(n\ge\max(1,n_0)).$$
--
--   Correctness and termination hold at every size, including below the cost threshold. The cost includes primitive arithmetic and zero tests along the actual run. Padding and the depth sum have constants independent of size and entries. This bound is the computational part paired with the trace decomposition.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: deterministic O(n^ω) field operations for a fixed admissible exponent → one finite algebraic program with successful primitive-costed execution at every size, and E,C,n₀ before n,A, relative to a supplied achieved multiplier; reason: makes uniform Big-O and algebraic access explicit, counts zero tests and inversion guards, and leaves constants dependent only on the fixed field, exponent and implementation
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 7, Lemma 3.3 (proof continues on p. 8)

import Definitions.Def_OddPermSum_Evaluation_crossedSum
import Definitions.Def_OddPermSum_Evaluation_achievedExponent

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Lemma 3.3. A and its inverse are supplied for evaluating the crossed sum. -/
theorem crossed_sum_computation {F : Type*} [Field F] [CharP F 2]
    (ω : ℝ) (hω : 2 < ω) (hω3 : ω ≤ 3)
    (M : AlgebraicProgram F) (Cₘ : ℝ) (nₘ : ℕ)
    (hM : MultipliesWithin M ω Cₘ nₘ) :
    ∃ (E : AlgebraicProgram F) (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F), IsUnit A.det →
        ∃ (fuel : ℕ) (s : MachineState F),
          run E n (matrixEncoding A ++ matrixEncoding A⁻¹) fuel = some s ∧
          s.outputs = [crossedSum A A⁻¹] ∧
          (max 1 n₀ ≤ n → (s.cost : ℝ) ≤ C * (n : ℝ)^ω) := by sorry

end OddPermSum.Evaluation
