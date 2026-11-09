-- Prove2me | Theorems.Thm_OddPermSum_Evaluation_value_computation
-- name    : OddPermSum.Evaluation.value_computation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T07:23:30.3442+00:00
-- url     : https://prove2.me/theorems/e4f9cae7-a13b-4864-bd92-80ce0d743d00
-- title:
--   Proposition 3.6 — scalar evaluation at every rank
-- statement:
--   Fix a characteristic-two field $F$, an achieved exponent $2<\omega\le3$, and a supplied uniformly costed multiplication program. There exist one finite deterministic program $E$ and uniform $C>0,n_0$ such that for all $n$ and every matrix $A\in F^{n\times n}$, the execution terminates and returns
--
--   $$\Phi(A),\qquad \operatorname{cost}_E(n,A)\le Cn^\omega\quad(n\ge\max(1,n_0)).$$
--
--   No invertibility or rank assumption is made. Correctness includes $n=0,1$ and all sizes below $n_0$. Constants may depend on the fixed field, exponent and supplied multiplication implementation only. This is the scalar all-rank result used alongside the gradient identities.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → increasing zero-based Fin n indices; reason: the order-preserving bijection changes no matrix, summation inequality or instance
--   - encoding: deterministic O(n^ω) field operations for a fixed admissible exponent → one finite algebraic program with successful primitive-costed execution at every size, and E,C,n₀ before n,A, relative to a supplied achieved multiplier; reason: makes uniform Big-O and algebraic access explicit, counts zero tests and inversion guards, and leaves constants dependent only on the fixed field, exponent and implementation
-- source:
--   Boxuan Chen, Bin Cui, Hanqing Li, Xupeng Miao, Haoze Wang, STOC 2027 submission #716 (October 2026), p. 9, Proposition 3.6 (proof continues on p. 10)

import Definitions.Def_OddPermSum_Evaluation_phi
import Definitions.Def_OddPermSum_Evaluation_achievedExponent

set_option autoImplicit false

namespace OddPermSum.Evaluation

/-- Proposition 3.6, with termination at all sizes and no rank restriction. -/
theorem value_computation {F : Type*} [Field F] [CharP F 2]
    (ω : ℝ) (hω : 2 < ω) (hω3 : ω ≤ 3)
    (M : AlgebraicProgram F) (Cₘ : ℝ) (nₘ : ℕ)
    (hM : MultipliesWithin M ω Cₘ nₘ) :
    ∃ (E : AlgebraicProgram F) (C : ℝ) (n₀ : ℕ), 0 < C ∧
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
        ∃ (fuel : ℕ) (s : MachineState F),
          run E n (matrixEncoding A) fuel = some s ∧
          s.outputs = [phi A] ∧
          (max 1 n₀ ≤ n → (s.cost : ℝ) ≤ C * (n : ℝ)^ω) := by sorry

end OddPermSum.Evaluation
