-- Prove2me | Theorems.Thm_FreeWeaver_Walk_theorem_3_2
-- name    : FreeWeaver.Walk.theorem_3_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:32:04.634096+00:00
-- url     : https://prove2.me/theorems/dc0c545c-2dd3-49e2-90bd-9a275f5ffe5c
-- title:
--   Theorem 3.2 — a bounded energy keeps z at distance at least 1/(4√b μ²) from the spectrum
-- statement:
--   For every pencil $\mathcal Y$ and threshold $z>\lambda_+(\mathcal Y)$, with $b=\operatorname{Tr}G_2$ and $\mu=1+\sigma_\Omega^2b$,
--   $$z-\lambda_+(\mathcal Y)\ \ge\ \frac1{4\sqrt b\,\mu^2}.$$
--   A bound on the energy thus keeps the threshold away from the spectrum; this is what makes the potential a barrier.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 20, Theorem 3.2

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 20, Theorem 3.2 (A bounded energy keeps z away from
the spectrum): "Let Y be a pencil and z > λ+(Y), and put b = Tr G2 and μ = 1 + σΩ^2 b. Then
z − λ+(Y) ≥ 1/(4√b μ^2). (3.2)" -/
theorem theorem_3_2 {ι J H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (Y : Pencil ι J) (hY : Y.IsHerm) (z : ℝ) (hz : upperEdge (Y.op s) < z) :
    let b : ℝ := (Y.resMoment s ω z 2).trace.re
    let μ : ℝ := 1 + Y.varSq * b
    1 / (4 * Real.sqrt b * μ ^ 2) ≤ z - upperEdge (Y.op s) := by sorry

end FreeWeaver.Walk
