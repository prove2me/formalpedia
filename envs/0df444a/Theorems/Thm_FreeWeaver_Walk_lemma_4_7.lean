-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_4_7
-- name    : FreeWeaver.Walk.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:36:22.128847+00:00
-- url     : https://prove2.me/theorems/05c3b41d-c86e-49ac-ae9d-0faadac5ea3c
-- title:
--   Lemma 4.7 — at a vertex Y(σ) = Ȟ(σ) ⊗ I; at the origin z₀ is √(uε) above the spectrum and ℱ(0, z₀) ≤ B
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb C^m$ be nonzero with $\sum_iv_iv_i^*=I_m$, $m\ge1$, $u=128$, and let $c$ be one of the two profiles. (a) For every vertex $\sigma\in\{-1,1\}^n$, $\mathcal Y(\sigma)=\check H(\sigma)\otimes I$, so $z>\lambda_+(\mathcal Y(\sigma))$ if and only if $\|\sum_i\sigma_iA_i\|<z$. (b) For every $\varepsilon\ge\max_i\|v_i\|^2$,
--   $$z_0-\lambda_+(\mathcal Y(0))\ge\sqrt{u\varepsilon},\qquad\mathcal F(0,z_0)\le B,$$
--   so $z_0>\lambda_+(\mathcal Y(0))$. The walk starts at $(0,z_0)$ within budget, and at a vertex the threshold bounds the discrepancy.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: ℂ^D with D = 2m, block-diagonal matrices with m × m blocks; the index set [n] × {0,1,2,3} → matrices indexed by Fin 2 × Fin m (I₂ ⊗ A is 1 ⊗ₖ A), the family indexed by Fin n × Fin 4, vectors indexed by Fin n from 0; reason: relabelling of the same coordinates
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 26, Lemma 4.7

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil
import Definitions.Def_FreeWeaver_Walk_Weaver
import Definitions.Def_FreeWeaver_Walk_FreeModel

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 26, Lemma 4.7 (The origin and the vertices): "(a) If x = σ ∈ {−1, 1}^n is a vertex,
then Y(σ) = Ȟ(σ) ⊗ I, so z > λ+(Y(σ)) if and only if ∥Σ_i σi Ai∥ < z. (b) z0 − λ+(Y(0)) ≥ √(uε)
and ℱ(0, z0) ≤ B, so z0 > λ+(Y(0)) and the potential is within budget at (0, z0)."
Standing assumptions of §4.1: `v_1, …, v_n ∈ ℂ^m` nonzero with `Σ_i v_i v_i* = I_m`, `D = 2m ≥ 1`,
`ε ≥ max_i ‖v_i‖²`; `u = 128`, and `c` is one of the two profiles of Definition 4.1. -/
theorem lemma_4_7 {n m : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (hm : 1 ≤ m) (v : Fin n → Fin m → ℂ) (hv0 : ∀ i, v i ≠ 0)
    (hP : IsParseval v) (s : Fin n × Fin 4 → H →L[ℂ] H) (ω : H)
    (hs : IsStdFreeSemicircular s ω) (c : ℝ → ℝ) (hc : IsProfile 128 c) :
    -- (a)
    (∀ σ : Fin n → ℝ, IsSigns σ →
      (freeModel c v σ).op s =
          CStarMatrix.ofMatrix (fun k l => Hcheck v σ k l • (1 : H →L[ℂ] H)) ∧
        ∀ z : ℝ, edge c v s σ < z ↔ opNorm (signedSum v σ) < z) ∧
    -- (b)
    (∀ ε : ℝ, (∀ i, sqNorm (v i) ≤ ε) →
      Real.sqrt (128 * ε) ≤ zStart 128 ε - edge c v s 0 ∧
        potential c v s ω 0 (zStart 128 ε) ≤ budget 128 ε ∧
        edge c v s 0 < zStart 128 ε) := by sorry

end FreeWeaver.Walk
