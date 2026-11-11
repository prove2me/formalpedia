-- Prove2me | Theorems.Thm_FreeWeaver_Walk_lemma_3_5
-- name    : FreeWeaver.Walk.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:32:03.795694+00:00
-- url     : https://prove2.me/theorems/2385fb12-340a-48ac-9bdf-3ecb03c73aac
-- title:
--   Lemma 3.5 — outward comparison: G as a subsolution of Ỹ at z̃ gives z̃ − λ₊(Ỹ) ≥ 1/(4√b μ²), G̃ ⪯ G, Tr G̃₂ ≤ b
-- statement:
--   Let $\mathcal Y,\tilde{\mathcal Y}$ be pencils on the same $\mathbb C^D$ with means $V,\tilde V$ and covariance maps $\Omega,\tilde\Omega$, such that $\Omega-\tilde\Omega$ maps positive semidefinite matrices to positive semidefinite matrices and $\langle M,(\Omega-\tilde\Omega)(M)\rangle\ge0$ for every Hermitian $M$. Let $z>\lambda_+(\mathcal Y)$, $G=G_1$, $U=G_2$ of $\mathcal Y$ at $z$, $b=\operatorname{Tr}U$, $\mu=1+\|\Omega(I)\|b$, and let $\tilde z\in\mathbb R$ satisfy $\tilde zI-\tilde V-\tilde\Omega(G)\succeq G^{-1}$. Then (a) $\tilde z-\lambda_+(\tilde{\mathcal Y})\ge 1/(4\sqrt b\mu^2)$, so $\tilde z>\lambda_+(\tilde{\mathcal Y})$; (b) $\tilde G\preceq G$; (c)
--   $$\operatorname{Tr}\tilde G_2\le b .$$
--   This is how boundary roundings and outward moves are accepted without computing a new resolvent.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
--   - generalization: Y and Ỹ are pencils over the free semicircular family fixed in §2.1 → Ỹ may be built on its own standard free semicircular family (index set J', Hilbert space H', vector ω'); reason: taking the same family for both pencils gives the paper's statement
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 21, Lemma 3.5

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), pp. 21–22, Lemma 3.5 (Outward comparison): "Let Y and Ỹ
be pencils, with means V, Ṽ and covariance maps Ω, Ω̃. Assume that Ω − Ω̃ maps positive
semidefinite matrices to positive semidefinite matrices and is a positive semidefinite operator on
H. Let z > λ+(Y), with resolvent moments G = G1 and U = G2 of Y at z, and put b = Tr U and
μ = 1 + ∥Ω(I)∥b. Let z̃ ∈ R satisfy z̃I − Ṽ − Ω̃(G) ⪰ G^{−1}, (3.3) that is, let G be a subsolution
of the matrix Dyson equation of Ỹ at the threshold z̃ (Definition 2.4). Then (a)
z̃ − λ+(Ỹ) ≥ 1/(4√b μ^2), so in particular z̃ > λ+(Ỹ), (b) the matrix resolvent G̃ of Ỹ at z̃
satisfies G̃ ⪯ G, and (c) the second resolvent moment G̃2 of Ỹ at z̃ satisfies Tr G̃2 ≤ b."
The two pencils share `D = card ι`; each is built on its own standard free semicircular family.
"Positive semidefinite operator on ℍ": `⟨M, (Ω − Ω̃)(M)⟩ = Tr(M*(Ω − Ω̃)(M)) ≥ 0` for every
Hermitian `M`. -/
theorem lemma_3_5 {ι J J' H H' : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [Fintype J'] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (s' : J' → H' →L[ℂ] H') (ω' : H') (hs' : IsStdFreeSemicircular s' ω')
    (Y : Pencil ι J) (hY : Y.IsHerm) (Y' : Pencil ι J') (hY' : Y'.IsHerm)
    (hpos : ∀ M : Matrix ι ι ℂ, M.PosSemidef → (Y.cov M - Y'.cov M).PosSemidef)
    (hpsd : ∀ M : Matrix ι ι ℂ, M.IsHermitian →
      0 ≤ (M.conjTranspose * (Y.cov M - Y'.cov M)).trace.re)
    (z : ℝ) (hz : upperEdge (Y.op s) < z) (z' : ℝ)
    (hsub : ((z' : ℂ) • (1 : Matrix ι ι ℂ) - Y'.V - Y'.cov (Y.resMoment s ω z 1) -
      (Y.resMoment s ω z 1)⁻¹).PosSemidef) :
    let G := Y.resMoment s ω z 1
    let b : ℝ := (Y.resMoment s ω z 2).trace.re
    let μ : ℝ := 1 + opNorm (Y.cov 1) * b
    -- (a)
    (1 / (4 * Real.sqrt b * μ ^ 2) ≤ z' - upperEdge (Y'.op s') ∧ upperEdge (Y'.op s') < z') ∧
    -- (b)
    (G - Y'.resMoment s' ω' z' 1).PosSemidef ∧
    -- (c)
    (Y'.resMoment s' ω' z' 2).trace.re ≤ b := by sorry

end FreeWeaver.Walk
