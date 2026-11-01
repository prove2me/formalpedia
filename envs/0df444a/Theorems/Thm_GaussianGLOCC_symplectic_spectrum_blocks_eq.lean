-- Prove2me | Theorems.Thm_GaussianGLOCC_symplectic_spectrum_blocks_eq
-- name    : GaussianGLOCC.symplectic_spectrum_blocks_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:42.3368+00:00
-- url     : https://prove2.me/theorems/1cd85687-0f26-4435-93c5-489e77bcda1d
-- title:
--   Eq. (43): the blocks $A$ and $B$ of a pure-state CM have the same symplectic spectrum
-- statement:
--   Let $\gamma=\begin{pmatrix}A&C\\C^T&B\end{pmatrix}$ be the covariance matrix of a pure Gaussian state of $n\times n$ modes ($A$, $B$, $C$ real $2n\times 2n$), i.e. $\gamma\ge i\sigma$ and $-(\gamma\sigma)^2=\mathbb 1$. Then
--
--   1. $A\sigma A\sigma^T=\mathbb 1+C\sigma C^T\sigma$;
--   2. $B\sigma B\sigma^T=\mathbb 1+C^T\sigma C\sigma$;
--   3. $A$ and $B$ have the same symplectic spectrum: $s(A)=s(B)$.
--
--   This is part (a) of the proof of Lemma 1: after it, local symplectic transformations bring $A$ and $B$ to the same diagonal form $\bigoplus_k a_k\mathbb 1$.
--
--   Differences from the source:
--   - encoding: CM of a pure state → quantumCovariance γ (γ + iJ ⪰ 0, J = −σ) together with −(γσ)² = 𝟙; reason: these are exactly the CMs of pure Gaussian states (γ ≥ iσ, p.3; purity identity, Appendix A)
--   - encoding: symplectic spectrum of A and B → sympSpec, the ascending vector of moduli of eigenvalues of σM, each listed once; reason: the p.3 definition of the symplectic spectrum, with the ordering of Lemma 2
--   - encoding: σ = ⊕ σ₁, σ₁ = [[0, −1], [1, 0]] (eq. (4)) and symplectic matrices S σ Sᵀ = σ → GaussianGLOCC.sigma n = −interleavedSymplecticForm n (the paper's σ); symplecticity is the published isSymplectic for J = −σ; reason: S σ Sᵀ = σ and S J Sᵀ = J define the same group, so no instance changes
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Appendix A (a), eqs. (40), (42), (43), p.11

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
import Definitions.Def_GaussianGLOCC_sympSpec
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (quantumCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, Appendix A (a), eqs. (40), (42),
(43), p.11: for the CM `γ = [[A, C], [Cᵀ, B]]` (40) of a pure state of `n × n` modes,
"From the two diagonal blocks we obtain AσAσᵀ = 𝟙 + CσCᵀσ, BσBσᵀ = 𝟙 + CᵀσCσ. (43) […] it
follows that A and B have the same symplectic spectrum."

Let `γ` be a `(n + n)`-mode covariance matrix (`γ ≥ iσ`) with `−(γσ)² = 𝟙`, and let
`A`, `C`, `B` be its A–A, A–B and B–B blocks. Then
1. `AσAσᵀ = 𝟙 + CσCᵀσ`,
2. `BσBσᵀ = 𝟙 + CᵀσCσ`,
3. `A` and `B` have the same (ascending) symplectic spectrum.

**Formalization Note.** "CM of a pure state" is encoded as `quantumCovariance γ`
(`γ + iJ ⪰ 0` with the published `J = −σ`, the same set as `γ ≥ iσ`) together with the purity
identity `−(γσ)² = 𝟙` (Appendix A, first sentence); these are exactly the CMs of pure Gaussian
states. `σ` is the paper's `σ`; in the A/B layout `σ_{2n}` restricted to each block is `σ_n`. -/
theorem symplectic_spectrum_blocks_eq {n : ℕ} (γ : Cov (n + n)) (hγ : quantumCovariance γ)
    (hpure : -(γ * sigma (n + n)) ^ 2 = 1) :
    blockA γ * sigma n * blockA γ * (sigma n).transpose =
        1 + blockC γ * sigma n * (blockC γ).transpose * sigma n ∧
      blockB γ * sigma n * blockB γ * (sigma n).transpose =
        1 + (blockC γ).transpose * sigma n * blockC γ * sigma n ∧
      sympSpec (blockA γ) = sympSpec (blockB γ) := by sorry

end GaussianGLOCC
