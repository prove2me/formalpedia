-- Prove2me | Theorems.Thm_FreeWeaver_Walk_theorem_7_1
-- name    : FreeWeaver.Walk.theorem_7_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:36:21.080203+00:00
-- url     : https://prove2.me/theorems/a05105f8-a4f6-45b0-97ee-b6f2834ab934
-- title:
--   Theorem 7.1 — averaged curvature over a finitely-valued centered random vector orthogonal to x
-- statement:
--   In the setting of §6 assume (7.1) with some $L>0$ and $u=128$, and let $\mathfrak m=\sum_{i\text{ live}}c_iq_i^2$. There is a centered random vector $y\in\mathbb R^k$ taking finitely many values, whose direction $h$ (Definition D.2) has $x^Th=0$ for every value, such that
--   $$uD\,\mathbb E\,\mathcal F''[h,h]\le-4u\mathfrak m+4L(1+13\mathfrak m)+8\sqrt{\mathfrak m(1+13\mathfrak m)}+\tfrac{560}3\mathfrak m,$$
--   and $\mathbb E\|h\|_2^2\le2k(z+\|\mathcal Y(x)\|)^2$.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: a centered random vector y ∈ ℝ^k taking finitely many values; E → finitely many values y_j ∈ ℝ^n supported on the live set with probabilities p_j ≥ 0, Σ p_j = 1, Σ p_j y_j = 0; E as the weighted sum; reason: a finitely-valued random vector is exactly such a list
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 33, Theorem 7.1

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 33, Theorem 7.1 (Averaged curvature): "Assume (7.1) holds. Then there is a centered
random vector y ∈ R^k, taking finitely many values, whose direction h has x^T h = 0 for every value
and satisfies u D · E ℱ''[h, h] ≤ −4u𝔪 + 4L(1 + 13𝔪) + 8√(𝔪(1 + 13𝔪)) + (560/3)𝔪. (7.2)
Moreover, E∥h∥_2^2 ≤ 2k(z + ∥Y(x)∥)^2."
Setting of §6 and assumption (7.1) with `L > 0`, `u = 128`, `D = 2m`. The random vector is a finite
list of values `y_j` (vectors of `ℝ^n` supported on the live set, i.e. vectors of `ℝ^k`) with
probabilities `p_j`; its direction is that of Definition D.2 (`dirOf`); `‖Y(x)‖` is the operator
norm on `ℂ^D ⊗ H`. -/
theorem theorem_7_1 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (c : ℝ → ℝ) (hc : IsProfile 128 c)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z : ℝ) (hz : edge c v s x < z)
    (hk : ∃ i, |x i| < 1)
    (hsmooth : ∀ i, |x i| < 1 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c (x i))
    (L : ℝ) (hL : 0 < L) (h71 : Assumption71 c v s ω x z 128 L) :
    let ms := mass c v s ω x z
    ∃ (N : ℕ) (p : Fin N → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
      (∀ j i, ¬ |x i| < 1 → y j i = 0) ∧
      ∑ j, p j • y j = 0 ∧
      (∀ j, ∑ i, x i * dirOf c v s ω x z 128 (y j) i = 0) ∧
      128 * (2 * (m : ℝ)) * ∑ j, p j * secondVar c v s ω x z (dirOf c v s ω x z 128 (y j)) ≤
        -4 * 128 * ms + 4 * L * (1 + 13 * ms) + 8 * Real.sqrt (ms * (1 + 13 * ms)) +
          560 / 3 * ms ∧
      ∑ j, p j * ∑ i, dirOf c v s ω x z 128 (y j) i ^ 2 ≤
        2 * (numLive x : ℝ) * (z + ‖(freeModel c v x).op s‖) ^ 2 := by sorry

end FreeWeaver.Walk
