-- Prove2me | Theorems.Thm_FreeWeaver_Walk_theorem_2_5_a
-- name    : FreeWeaver.Walk.theorem_2_5_a
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:31:51.002919+00:00
-- url     : https://prove2.me/theorems/137d8f8e-595c-4f5a-b8d6-3b8f7ae9ea3e
-- title:
--   Theorem 2.5(a) — Lehner's upper bound λ₊(Y) ≤ λmax(V + Z⁻¹ + Ω(Z)) for every Z ≻ 0
-- statement:
--   For every pencil $\mathcal Y$ and every positive definite $D\times D$ matrix $Z$,
--   $$\lambda_+(\mathcal Y)\le\lambda_{\max}\big(V+Z^{-1}+\Omega(Z)\big).$$
--   This is the second fact taken from the literature (Lehner); the paper uses only part (a) of Theorem 2.5.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 15, Theorem 2.5(a)

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 15, Theorem 2.5(a) (Lehner's formula): "Let Y be a
pencil. (a) For every positive definite D × D matrix Z, λ+(Y) ≤ λmax(V + Z^{−1} + Ω(Z)). (2.5)"
`λ₊` is the supremum of the real spectrum of the operator, `λmax` that of the Hermitian matrix. -/
theorem theorem_2_5_a {ι J H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (Y : Pencil ι J) (hY : Y.IsHerm) (Z : Matrix ι ι ℂ) (hZ : Z.PosDef) :
    upperEdge (Y.op s) ≤ lamMax (Y.V + Z⁻¹ + Y.cov Z) := by sorry

end FreeWeaver.Walk
