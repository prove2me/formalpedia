-- Prove2me | Theorems.Thm_FreeWeaver_Walk_proposition_2_11
-- name    : FreeWeaver.Walk.proposition_2_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:31:57.374763+00:00
-- url     : https://prove2.me/theorems/0f7919de-0369-4be4-bc49-3608a8bd3ec1
-- title:
--   Proposition 2.11 — the fixed-point iteration decreases geometrically to G⁻¹; G is the smallest subsolution
-- statement:
--   Let $z>\lambda_+(\mathcal Y)$, $b=\operatorname{Tr}G_2$, $\mu=1+\sigma_\Omega^2b$, and $\Theta^{(0)}=zI-V$, $\Theta^{(d+1)}=zI-V-\Omega((\Theta^{(d)})^{-1})$. (a) Every $\Theta^{(d)}$ is positive definite and $G^{-1}\preceq\Theta^{(d+1)}\preceq\Theta^{(d)}\preceq\Theta^{(0)}\preceq(z+\|V\|)I$, with $z+\|V\|>0$. (b) For every $d\ge0$,
--   $$0\preceq\Theta^{(d)}-G^{-1}\preceq(z+\|V\|)\,\mu\,(1-\mu^{-1})^{d+1}I,$$
--   and $\Theta^{(d)}\to G^{-1}$. (c) If $Z$ is a subsolution at $z$, then $\Theta^{(d)}\succeq Z^{-1}$ for every $d$ and $G\preceq Z$.
--   The iteration is how the walk computes the matrix resolvent and the potential.
--
--   Differences from the source:
--   - encoding: a standard free semicircular family in a C*-probability space (A, τ), represented on H with τ(a) = ⟨ω, aω⟩; ℂ^D ⊗ H → IsStdFreeSemicircular s ω on a complex Hilbert space H (unit ω, self-adjoint s_γ with the semicircle moments, freeness of the polynomial algebras of the s_γ, τ tracial and faithful on the generated C*-algebra); operators on ℂ^D ⊗ H as CStarMatrix ι ι (H →L[ℂ] H), D = card ι ≥ 1; id ⊗ τ as the matrix of ⟨ω, T_kl ω⟩; λ₊ = sSup of the real spectrum; reason: the paper's own realization (p. 13); faithfulness makes the spectrum and norm those of the abstract C*-algebra, so no instance changes
--   - encoding: the order ⪯ of Hermitian matrices → A ⪯ B is (B − A).PosSemidef; ≻ 0 is PosDef; ‖·‖ of a matrix is the ℓ² operator norm (opNorm); Tr G₂ is the real part of the trace; reason: Lean conventions for the same objects; Tr G₂ is real because G₂ is Hermitian
--   - encoding: the Θ(d) decrease to G⁻¹ → the chain of (a) together with Filter.Tendsto Θ atTop (nhds G⁻¹) in the entrywise topology; reason: all norms on D × D matrices give the same convergence
-- source:
--   Kathuria, A Walk From Free Probability to Matrix Discrepancy II, arXiv:2609.18913 (version dated November 3, 2026; sha256 c06bf728…), p. 19, Proposition 2.11

import Mathlib
import Definitions.Def_FreeWeaver_Walk_Pencil

open scoped ComplexOrder

namespace FreeWeaver.Walk

/-- Kathuria, *A Walk From Free Probability to Matrix Discrepancy II*, arXiv:2609.18913 (version
dated November 3, 2026; sha256 c06bf728…), p. 19, Proposition 2.11 (The fixed-point iteration):
"Let z > λ+(Y), b = Tr G2 and μ = 1 + σΩ^2 b, and define Θ(0) = zI − V,
Θ(d+1) = zI − V − Ω((Θ(d))^{−1}). (2.7) (a) Every Θ(d) is positive definite, and
G^{−1} ⪯ Θ(d+1) ⪯ Θ(d) ⪯ Θ(0) ⪯ (z + ∥V∥)I, with z + ∥V∥ > 0. (b) For every d ≥ 0,
0 ⪯ Θ(d) − G^{−1} ⪯ (z + ∥V∥) μ (1 − μ^{−1})^{d+1} I. (2.8) In particular the Θ(d) decrease to
G^{−1}. (c) If Z is a subsolution of the matrix Dyson equation of Y at the threshold z, then
Θ(d) ⪰ Z^{−1} for every d, and G ⪯ Z." -/
theorem proposition_2_11 {ι J H : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] [Fintype J]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : J → H →L[ℂ] H) (ω : H) (hs : IsStdFreeSemicircular s ω)
    (Y : Pencil ι J) (hY : Y.IsHerm) (z : ℝ) (hz : upperEdge (Y.op s) < z) :
    let G := Y.resMoment s ω z 1
    let b : ℝ := (Y.resMoment s ω z 2).trace.re
    let μ : ℝ := 1 + Y.varSq * b
    let Θ := Y.fpIter z
    -- (a)
    ((∀ d, (Θ d).PosDef ∧ (Θ (d + 1) - G⁻¹).PosSemidef ∧ (Θ d - Θ (d + 1)).PosSemidef ∧
        (Θ 0 - Θ d).PosSemidef) ∧
      (((z + opNorm Y.V : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - Θ 0).PosSemidef ∧
      0 < z + opNorm Y.V) ∧
    -- (b)
    ((∀ d : ℕ, (Θ d - G⁻¹).PosSemidef ∧
        (((z + opNorm Y.V) * μ * (1 - μ⁻¹) ^ (d + 1) : ℝ) • (1 : Matrix ι ι ℂ) -
          (Θ d - G⁻¹)).PosSemidef) ∧
      Filter.Tendsto Θ Filter.atTop (nhds G⁻¹)) ∧
    -- (c)
    (∀ Z : Matrix ι ι ℂ, Y.IsSubsolution z Z →
      (∀ d, (Θ d - Z⁻¹).PosSemidef) ∧ (Z - G).PosSemidef) := by sorry

end FreeWeaver.Walk
