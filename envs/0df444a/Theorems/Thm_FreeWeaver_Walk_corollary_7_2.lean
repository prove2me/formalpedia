-- Prove2me | Theorems.Thm_FreeWeaver_Walk_corollary_7_2
-- name    : FreeWeaver.Walk.corollary_7_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:36:14.830952+00:00
-- url     : https://prove2.me/theorems/ffbc3dd8-7873-4eb5-b5a6-900a2989a741
-- title:
--   Corollary 7.2 — negative curvature orthogonal to x when 𝔪 ≥ 1/16
-- statement:
--   Let $u=128$, assume (7.1) with $0<L\le2/0.999^2$ and $\mathfrak m\ge1/16$. Then the random direction of Theorem 7.1 satisfies $uD\,\mathbb E\,\mathcal F''[h,h]\le-3$, and there is a unit vector $h$ supported on the live set with $x^Th=0$ and
--   $$\mathcal F''[h,h]\le-\frac{3}{2uDk(z+\|\mathcal Y(x)\|)^2}.$$
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
--   - encoding: the random direction of Theorem 7.1 → some finitely-valued random vector with every conclusion of Theorem 7.1 (centered, orthogonal, (7.2), the second-moment bound) and uD E ℱ''[h,h] ≤ −3; reason: Theorem 7.1 is stated existentially; its vector is the one meant
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 34, Corollary 7.2

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 34, Corollary 7.2 (Negative curvature orthogonal to x): "Let u = 128, assume (7.1)
with L ≤ 2/0.999^2, and assume 𝔪 ≥ 1/16. Then the random direction of Theorem 7.1 satisfies
u D · E ℱ''[h, h] ≤ −3. Consequently, there is a unit vector h, supported on I, with x^T h = 0 and
ℱ''[h, h] ≤ −3/(2uDk(z + ∥Y(x)∥)^2)."
Setting of §6; the first clause asserts a random vector with every property of Theorem 7.1 and the
bound `−3`. -/
theorem corollary_7_2 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (c : ℝ → ℝ) (hc : IsProfile 128 c)
    (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 1) (z : ℝ) (hz : edge c v s x < z)
    (hk : ∃ i, |x i| < 1)
    (hsmooth : ∀ i, |x i| < 1 → ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c (x i))
    (L : ℝ) (hL : 0 < L) (hL2 : L ≤ 2 / (0.999 : ℝ) ^ 2) (h71 : Assumption71 c v s ω x z 128 L)
    (hms : 1 / 16 ≤ mass c v s ω x z) :
    let ms := mass c v s ω x z
    (∃ (N : ℕ) (p : Fin N → ℝ) (y : Fin N → Fin n → ℝ),
      (∀ j, 0 ≤ p j) ∧ ∑ j, p j = 1 ∧
      (∀ j i, ¬ |x i| < 1 → y j i = 0) ∧
      ∑ j, p j • y j = 0 ∧
      (∀ j, ∑ i, x i * dirOf c v s ω x z 128 (y j) i = 0) ∧
      128 * (2 * (m : ℝ)) * ∑ j, p j * secondVar c v s ω x z (dirOf c v s ω x z 128 (y j)) ≤
        -4 * 128 * ms + 4 * L * (1 + 13 * ms) + 8 * Real.sqrt (ms * (1 + 13 * ms)) +
          560 / 3 * ms ∧
      ∑ j, p j * ∑ i, dirOf c v s ω x z 128 (y j) i ^ 2 ≤
        2 * (numLive x : ℝ) * (z + ‖(freeModel c v x).op s‖) ^ 2 ∧
      128 * (2 * (m : ℝ)) * ∑ j, p j * secondVar c v s ω x z (dirOf c v s ω x z 128 (y j)) ≤
        -3) ∧
    ∃ h : Fin n → ℝ, ∑ i, h i ^ 2 = 1 ∧ (∀ i, ¬ |x i| < 1 → h i = 0) ∧ ∑ i, x i * h i = 0 ∧
      secondVar c v s ω x z h ≤
        -3 / (2 * 128 * (2 * (m : ℝ)) * (numLive x : ℝ) *
          (z + ‖(freeModel c v x).op s‖) ^ 2) := by sorry

end FreeWeaver.Walk
