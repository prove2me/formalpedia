-- Prove2me | Theorems.Thm_FreeWeaver_Walk_theorem_2_3
-- name    : FreeWeaver.Walk.theorem_2_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:31:49.968584+00:00
-- url     : https://prove2.me/theorems/24b2f7d0-06cd-444f-86e1-3e6ecc0bed85
-- title:
--   Theorem 2.3 — the matrix Dyson equation for every pencil
-- statement:
--   Let $\mathcal Y=V\otimes I+\sum_\gamma K_\gamma\otimes s_\gamma$ be a pencil over a standard free semicircular family, with $D\ge1$ coordinates. For every complex $w$ with $\operatorname{Im}w>0$ the operator $wI-\mathcal Y$ is invertible and $G(w)=(\mathrm{id}\otimes\tau)(wI-\mathcal Y)^{-1}$ satisfies
--   $$\big(wI-V-\Omega(G(w))\big)G(w)=I .$$
--   For every real $z>\lambda_+(\mathcal Y)$ the matrix resolvent $G=G(z)$ is positive definite and
--   $$G^{-1}=zI-V-\Omega(G).$$
--   This is the first of the two facts the paper takes from the literature (Haagerup–Thorbjørnsen); every later identity for the energy and the iteration is derived from it.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 15, Theorem 2.3

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 15, Theorem 2.3 (The matrix Dyson equation): "Let Y
be a pencil. For every complex number w with Im w > 0, the operator wI − Y is invertible, and the
matrix G(w) = (id ⊗ τ)(wI − Y)^{−1} satisfies (wI − V − Ω(G(w))) G(w) = I. (2.2) For every real
z > λ+(Y), the matrix resolvent G = G(z) is positive definite and satisfies the matrix Dyson
equation G^{−1} = zI − V − Ω(G). (2.3)" Here `Y` is any pencil with Hermitian mean and
coefficients over any standard free semicircular family `(s, ω)` on a Hilbert space `H`, with
`D = card ι ≥ 1`. -/
theorem theorem_2_3 {ι J H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (Y : Pencil ι J) (hY : Y.IsHerm) :
    (∀ w : ℂ, 0 < w.im →
      IsUnit (w • (1 : CStarMatrix ι ι (H →L[ℂ] H)) - Y.op s) ∧
      (w • (1 : Matrix ι ι ℂ) - Y.V - Y.cov (Y.stieltjes s ω w)) * Y.stieltjes s ω w = 1) ∧
    (∀ z : ℝ, upperEdge (Y.op s) < z →
      (Y.resMoment s ω z 1).PosDef ∧
      (Y.resMoment s ω z 1)⁻¹ = (z : ℂ) • (1 : Matrix ι ι ℂ) - Y.V - Y.cov (Y.resMoment s ω z 1)) := by sorry

end FreeWeaver.Walk
