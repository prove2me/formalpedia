-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_8_2
-- name    : FreeWeaver.Walk.lemma_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:37:42.185896+00:00
-- url     : https://prove2.me/theorems/7aa13059-fb6a-4047-ac8b-6e4ba4e92210
-- title:
--   Lemma 8.2 — final rounding: signs extending the frozen coordinates with ‖Σσ_iA_i‖ < z(1 + ½√(𝔪/u)), found by Algorithm 1 in O(nm²) operations
-- statement:
--   Let $u=128$, let $c$ satisfy $c(t)\ge u(1-t^2)$ on $[-1,1]$, let $x\in[-1,1]^n$ and $z>\lambda_+(\mathcal Y(x))$, and $\mathfrak m=\sum_{i\text{ live}}c_iq_i^2$. Then signs $\sigma$ with $\sigma_i=x_i$ for every frozen $i$ and
--   $$\Big\|\sum_i\sigma_iA_i\Big\|<z\Big(1+\tfrac12\sqrt{\mathfrak m/u}\Big)$$
--   exist, and Algorithm 1 returns such signs. Moreover one universal constant $C$ and one deterministic program of the real RAM compute Algorithm 1's output within $C(nm^2+1)$ steps on the input $(n,m,\operatorname{Re}/\operatorname{Im}\,v,x)$.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - generalization: c a variance function (in §4–§9 one of the profiles of Definition 4.1) with c(t) ≥ u(1 − t²) on [−1, 1] → any c : ℝ → ℝ with that bound (the free model is built from c); reason: the lemma states no other condition on c; both profiles satisfy the bound by (4.2), so the statement specializes to the paper's
--   - encoding: Algorithm 1 finds them with O(nm²) arithmetic operations → ∃ C : ℕ and one FewInnerTSP-admissible program P of the MatMulTimeLP real RAM, fixed before the input, halting on roundInput n m v x at t with t + 1 ≤ C·(n·m² + 1) and outputting roundAlg v x; reason: O(·) with an explicit universal constant; every executed instruction (index bookkeeping, input reads) is counted, so this implies the count of arithmetic operations
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 34, Lemma 8.2

import Mathlib
import Definitions.Def_MatMulTimeLP_RealRAM
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel
import Definitions.Def_FreeWeaver_Walk_Walk

open scoped ComplexOrder

universe u

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 34, Lemma 8.2 (Final rounding): "Let z > λ+(Y(x)), and assume c(t) ≥ u(1 − t^2) on
[−1, 1]. Let 𝔪 = Σ_{i live} ci qi^2. Then signs σ ∈ {−1, 1}^n with σi = xi for every frozen i and
∥Σ_i σi Ai∥ < z(1 + (1/2)√(𝔪/u)) (8.1) exist, and Algorithm 1 finds them with O(nm^2) arithmetic
operations."
First clause: for every state `x` and variance function `c` with `c(t) ≥ u(1 − t²)` on `[−1, 1]`
(`u = 128`), such signs exist, and the output `roundAlg v x` of Algorithm 1 is such signs. Second
clause (the `O(nm²)`): one universal constant `C` and one admissible program of the published real
RAM which, on the input `[n, m, Re/Im of the v_i, x_1, …, x_n]`, halts within `C (n m² + 1)` steps
and outputs Algorithm 1's signs. Standing assumptions of §4.1 on `v`. -/
theorem lemma_8_2 :
    (∀ {n m : ℕ} {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (v : Fin n → Fin m → ℂ), 1 ≤ m → (∀ i, v i ≠ 0) → IsParseval v →
      ∀ (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H), IsStdFreeSemicircular s ω →
      ∀ (c : ℝ → ℝ), (∀ t : ℝ, -1 ≤ t → t ≤ 1 → 128 * (1 - t ^ 2) ≤ c t) →
      ∀ (x : Fin n → ℝ), (∀ i, |x i| ≤ 1) → ∀ z : ℝ, edge c v s x < z →
        (∃ σ : Fin n → ℝ, IsSigns σ ∧ (∀ i, ¬ |x i| < 1 → σ i = x i) ∧
          opNorm (signedSum v σ) < z * (1 + 1 / 2 * Real.sqrt (mass c v s ω x z / 128))) ∧
        (IsSigns (roundAlg v x) ∧ (∀ i, ¬ |x i| < 1 → roundAlg v x i = x i) ∧
          opNorm (signedSum v (roundAlg v x)) <
            z * (1 + 1 / 2 * Real.sqrt (mass c v s ω x z / 128)))) ∧
    ∃ (C : ℕ) (P : MatMulTimeLP.Program), FewInnerTSP.Admissible P ∧
      ∀ (n m : ℕ) (v : Fin n → Fin m → ℂ), 1 ≤ m → (∀ i, v i ≠ 0) → IsParseval v →
      ∀ (x : Fin n → ℝ), (∀ i, |x i| ≤ 1) → ∀ tape : MatMulTimeLP.Tape,
        ∃ t : ℕ, MatMulTimeLP.HaltsAt P (roundInput n m v x) tape t ∧
          t + 1 ≤ C * (n * m ^ 2 + 1) ∧
          MatMulTimeLP.outputAt P (roundInput n m v x) tape t n = roundAlg v x := by sorry

end FreeWeaver.Walk
