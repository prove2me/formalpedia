-- Prove2me | Theorems.Thm_HolevoEntropyGain_lemma_2
-- name    : HolevoEntropyGain.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:39.392007+00:00
-- url     : https://prove2.me/theorems/b3a5ad15-f4da-4797-a2bb-98bf728d267c
-- title:
--   Lemma 2: the Gibbs state of $R\epsilon R^\top$ is Gaussian with $2\Delta^{-1}\alpha_\beta = \cot\beta\epsilon\Delta$, (17)–(19)
-- statement:
--   Let $W$ be an irreducible strongly continuous Weyl system for a nondegenerate skew-symmetric $\Delta$, let $\epsilon$ be a real positive definite $2s\times2s$ matrix, and let $F = R\epsilon R^\top$. For every $\beta>0$, $\operatorname{Tr}\exp(-\beta F)<\infty$, and the density operator $\rho_\beta = \exp(-\beta F - c(\beta))$ of (6) is the density operator of the nondegenerate Gaussian state with zero mean and covariance matrix $\alpha_\beta$ satisfying
--
--   $$
--   2\Delta^{-1}\alpha_\beta = \cot\beta\epsilon\Delta . \tag{17}
--   $$
--
--   Moreover,
--
--   $$
--   c(\beta) = \tfrac12\log\Big[\det\Big(\Delta^{-1}\alpha_\beta - \tfrac i2 I\Big)\Big], \tag{18}
--   $$
--
--   and the entropy is
--
--   $$
--   H(\rho_\beta) = \tfrac12\log\det\Big[\Delta^{-1}\alpha_\beta - \tfrac i2 I\Big] + \operatorname{Sp}\big[(\Delta^{-1}\alpha_\beta)\operatorname{arc\,cot}(2\Delta^{-1}\alpha_\beta)\big], \tag{19}
--   $$
--
--   where $\operatorname{Sp}$ denotes the trace of a $2s\times2s$ matrix. In particular $\sin(\beta\epsilon\Delta)$ is invertible and $H(\rho_\beta)<\infty$.
--
--   Lemma 2 identifies thermal states of quadratic Hamiltonians as Gaussian states and computes their entropy; the proof of Proposition 2 lets $\beta\to0$ in these formulas.
--
--   Differences from the source:
--   - encoding: a separable Hilbert space H carrying a representation of the CCR → ℓ²(I) with [Countable I] [Nonempty I]; reason: a representation space is nonzero and separable; on ℓ²(∅) = 0 there are no states and the statement would be about an empty set
--   - reading: the Weyl system giving the representation of the CCR → an irreducible, strongly continuous Weyl system (WeylSystem); reason: the Schrödinger representation (Stone–von Neumann); under the reducible reading Proposition 2 is false (W ⊗ I with id ⊗ trace-and-prepare)
--   - encoding: W(z) = exp(iRz) on Z of dimension 2s with commutation matrix Δ → W(z)W(w) = exp(−(i/2)zᵀΔw)W(z+w), Z = Fin (2*s) → ℝ, every nondegenerate skew-symmetric Δ; reason: [Rⱼ, Rₖ] = iΔⱼₖ; every statement is invariant under Δ ↦ −Δ, so the sign convention changes no instance
--   - encoding: F = RεRᵀ → spectral data (orthonormal basis eₙ, energies Eₙ) whose form equals Σⱼₖ εⱼₖ⟨Rⱼψ, Rₖψ⟩ on ∩ⱼ D(Rⱼ), Rⱼ the Stone generator of t ↦ W(teⱼ); the statement holds for every such datum; reason: Mathlib has no unbounded functional calculus; (5) forces discrete spectrum, so F has such data and every choice gives the same exp(−βF)
--   - encoding: cot βεΔ → cos(βεΔ)·sin(βεΔ)⁻¹ by power series, with det sin(βεΔ) ≠ 0 as part of the conclusion; reason: Lean's inverse is 0 on singular matrices; asserting invertibility excludes that default
--   - reading: Sp(Δ⁻¹α_β)arc cot(2Δ⁻¹α_β) → the trace of the product (Δ⁻¹α_β)·arccot(2Δ⁻¹α_β); reason: the other parse, a scalar times a matrix, is not a number; the one-mode case gives the thermal entropy
--   - encoding: Sp f(Δ⁻¹α_β) and det(Δ⁻¹α_β − (i/2)I) → sum over the characteristic roots of λ·arccot(2λ) with arccot z = (1/2i)log((z+i)/(z−i)), and Matrix.det; both logarithms via Complex.log; reason: Δ⁻¹α_β is diagonalizable with eigenvalues ±iαⱼ, so the root sum is the matrix trace; the determinant is a positive real, where Complex.log is the real log
--   - encoding: H(ρ_β) as a real number → extendedEntropyNats(ρ_β) < ⊤ and its toReal, cast to ℂ; reason: the finiteness clause makes toReal the entropy
--   - encoding: H(ρ) = Σλₖ(−log λₖ) and H(ρ‖σ) = Σλₖ[log λₖ − ⟨eₖ|log σ|eₖ⟩] in [0, +∞] → extendedEntropyNats / extendedRelativeEntropyNats, suprema over finite coordinate compressions in ℝ≥0∞; reason: equal for density operators by Lindblad's lemma; natural logarithm as in footnote 1
--   - reading: "the density operator ρβ given by (6)", which presupposes (5) for F = RεRᵀ → (5), Σₙ e^{−βEₙ} summable, stated as the first clause of the conclusion; reason: (6) defines a density operator only under (5) (p.3), so the lemma's subject exists only if (5) holds; the Appendix (p.8) exhibits ρβ = C exp(−RεRᵀ) as a Gaussian density operator, and no hypothesis (5) is added
-- source:
--   Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, Lemma 2, eqs. (17)–(19), p.5 (proof in the Appendix, p.8)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P07
import Definitions.Def_HolevoEntropyGain_IsCommutationMatrix
import Definitions.Def_HolevoEntropyGain_IsEnergySpectrum
import Definitions.Def_HolevoEntropyGain_IsGaussianState
import Definitions.Def_HolevoEntropyGain_IsNondegenerateCovariance
import Definitions.Def_HolevoEntropyGain_gibbsState
import Definitions.Def_HolevoEntropyGain_matrixCot
import Definitions.Def_HolevoEntropyGain_ratioMatrix
import Definitions.Def_HolevoEntropyGain_arccotTrace

open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Frontier18.P07 (extendedEntropyNats)

namespace HolevoEntropyGain

/-- Lemma 2: for `F = RεRᵀ` with `ε` positive definite and `β > 0`, (5) holds, and `ρ_β` of (6) is the
density operator of the nondegenerate Gaussian state with zero mean and covariance matrix `α` satisfying
`2Δ⁻¹α = cot βεΔ` (17). Moreover `c(β) = ½ log det(Δ⁻¹α - (i/2)I)` (18), and the entropy is
`H(ρ_β) = ½ log det(Δ⁻¹α - (i/2)I) + Sp[(Δ⁻¹α) arc cot(2Δ⁻¹α)]` (19)
(Holevo, The entropy gain of infinite-dimensional quantum channels, arXiv:1003.5765v1, §3, Lemma 2, eqs. (17)–(19), p.5, PDF p.5).

**Formalization Note** The theorem is for every spectral datum of `F` (R10), and `(5)` is part of the
conclusion. `sin βεΔ` is invertible, also part of the conclusion, so `cot` has no default value; since
`Δ` is invertible, (17) determines `α`. The determinant in (18)–(19) is a positive real, so
`Complex.log` is the real logarithm. `Sp` is read through characteristic roots (R6). (5) is stated by
summability of a nonnegative real series; finiteness of `H(ρ_β)` is stated before its real value. -/
theorem lemma_2 {I : Type} [Countable I] [Nonempty I] {s : ℕ}
    {Δ : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hΔ : IsCommutationMatrix Δ) (W : WeylSystem I Δ)
    {ε : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ} (hε : ε.PosDef)
    {e : HilbertBasis I ℂ (Hilbert I)} {E : I → ℝ} (hE : IsEnergySpectrum W ε e E)
    {β : ℝ} (hβ : 0 < β) :
    Summable (fun n => Real.exp (-β * E n)) ∧
      (matrixSin (β • (ε * Δ))).det ≠ 0 ∧
      ∃ α : Matrix (Fin (2 * s)) (Fin (2 * s)) ℝ,
        (2 : ℝ) • (Δ⁻¹ * α) = matrixCot (β • (ε * Δ)) ∧
        IsGaussianState W α (gibbsState e E β) ∧
        IsNondegenerateCovariance Δ α ∧
        (gibbsConstant E β : ℂ) =
          (1 / 2) * Complex.log (ratioMatrix Δ α - (Complex.I / 2) • 1).det ∧
        extendedEntropyNats (gibbsState e E β) < ⊤ ∧
        ((extendedEntropyNats (gibbsState e E β)).toReal : ℂ) =
          (1 / 2) * Complex.log (ratioMatrix Δ α - (Complex.I / 2) • 1).det +
            arccotTrace (ratioMatrix Δ α) := by sorry

end HolevoEntropyGain
