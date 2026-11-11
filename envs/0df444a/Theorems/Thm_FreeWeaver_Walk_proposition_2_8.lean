-- Prove2me | Theorems.Thm_FreeWeaver_Walk_proposition_2_8
-- name    : FreeWeaver.Walk.proposition_2_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:31:53.950205+00:00
-- url     : https://prove2.me/theorems/57b38171-897f-41cc-9c8e-7202a230baa8
-- title:
--   Proposition 2.8 — the energy identities X = I + Ω(G₂), G² ⪯ G₂, I ⪯ X ⪯ μI, M*(X) ⪯ (1 − μ⁻¹)X
-- statement:
--   Let $z>\lambda_+(\mathcal Y)$, $G=G_1$, $G_2$ the resolvent moments, $b=\operatorname{Tr}G_2$, $\mu=1+\sigma_\Omega^2b$, $X=G^{-1}G_2G^{-1}$, $\mathcal M(N)=G\Omega(N)G$ and $\mathcal M^*(N)=\Omega(GNG)$. Then (a) $X=I+\Omega(G_2)$, $G_2=G^2+\mathcal M(G_2)$ and $\mathcal M^*(X)=X-I$; (b) $G^2\preceq G_2$, $\|G\|^2\le\|G_2\|\le b$ and $I\preceq X\preceq\mu I$; (c)
--   $$\mathcal M^*(X)\preceq(1-\mu^{-1})X .$$
--   Part (c) is the contraction rate of the fixed-point iteration (Proposition 2.11).
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 17, Proposition 2.8

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 17, Proposition 2.8 (The energy): "Let z > λ+(Y),
b = Tr G2 and μ = 1 + σΩ^2 b. (a) X = I + Ω(G2). Equivalently, G2 = G^2 + M(G2). Moreover
M*(X) = X − I. (b) G^2 ⪯ G2, so ∥G∥^2 ≤ ∥G2∥ ≤ b. Also I ⪯ X ⪯ μI. (c) M*(X) ⪯ (1 − μ^{−1})X."
Here `G = G_1`, `G_2` are the resolvent moments at `z`, `X = G⁻¹ G_2 G⁻¹` is the energy matrix,
`M(N) = G Ω(N) G` and `M*(N) = Ω(G N G)` (§2.4, p. 17); `A ⪯ B` is `B − A` positive semidefinite. -/
theorem proposition_2_8 {ι J H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (Y : Pencil ι J) (hY : Y.IsHerm) (z : ℝ) (hz : upperEdge (Y.op s) < z) :
    let G := Y.resMoment s ω z 1
    let G2 := Y.resMoment s ω z 2
    let b : ℝ := G2.trace.re
    let μ : ℝ := 1 + Y.varSq * b
    let X := G⁻¹ * G2 * G⁻¹
    let Mmap : Matrix ι ι ℂ → Matrix ι ι ℂ := fun N => G * Y.cov N * G
    let Mstar : Matrix ι ι ℂ → Matrix ι ι ℂ := fun N => Y.cov (G * N * G)
    -- (a)
    (X = 1 + Y.cov G2 ∧ G2 = G ^ 2 + Mmap G2 ∧ Mstar X = X - 1) ∧
    -- (b)
    ((G2 - G ^ 2).PosSemidef ∧ opNorm G ^ 2 ≤ opNorm G2 ∧ opNorm G2 ≤ b ∧
      (X - 1).PosSemidef ∧ ((μ : ℂ) • (1 : Matrix ι ι ℂ) - X).PosSemidef) ∧
    -- (c)
    (((1 - μ⁻¹ : ℝ) : ℂ) • X - Mstar X).PosSemidef := by sorry

end FreeWeaver.Walk
