-- Prove2me | Theorems.Thm_GaussianGLOCC_pure_cm_sq
-- name    : GaussianGLOCC.pure_cm_sq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:50.243994+00:00
-- url     : https://prove2.me/theorems/d43f4788-47b9-4574-a234-3aa9be98bdb2
-- title:
--   Appendix A: purity of a Gaussian state implies $-(\gamma\sigma)^2=\mathbb 1$
-- statement:
--   Let $\rho$ be a pure Gaussian state of $n$ bosonic modes with covariance matrix $\gamma$ (vacuum CM $\mathbb 1$), and let $\sigma$ be the symplectic matrix of eq. (4). Then
--
--   $$
--   -(\gamma\sigma)^2=\mathbb 1 .
--   $$
--
--   The identity is the starting point of the proof of the standard form (Lemma 1): its block form (42) gives the relations (43) between the blocks of $\gamma$.
--
--   Differences from the source:
--   - generalization: pure state ρ of n × n modes (Lemma 1's setting) → pure Gaussian state of any number n of modes; reason: the identity holds for every pure Gaussian state; at 2n modes it is the page's claim
--   - encoding: σ = ⊕ σ₁, σ₁ = [[0, −1], [1, 0]] (eq. (4)) and symplectic matrices S σ Sᵀ = σ → GaussianGLOCC.sigma n = −interleavedSymplecticForm n (the paper's σ); symplecticity is the published isSymplectic for J = −σ; reason: S σ Sᵀ = σ and S J Sᵀ = J define the same group, so no instance changes
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Appendix A, p.11, first sentence

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
import Definitions.Def_GaussianGLOCC_SqueezedStates
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, *Entanglement transformations of pure Gaussian states*,
arXiv:quant-ph/0301038v1, Appendix A, p.11, first sentence: "Purity of the state ρ implies that
−(γσ)² = 𝟙."

If `ρ` is a pure Gaussian state of `n` modes with covariance matrix `γ`, then
`−(γσ)² = 𝟙`.

**Formalization Note.** `σ` is the paper's `σ = ⊕ [[0, −1], [1, 0]]` (eq. (4)), vacuum CM `𝟙`.
The paper states this for the `n × n`-mode states of Lemma 1; it holds for any number of
modes, and is stated so (`n` arbitrary, the bipartite case being `n + n`). -/
theorem pure_cm_sq {n : ℕ} (ρ : DensityKernel n) (γ : Cov n) (hρ : IsPureGaussian ρ γ) :
    -(γ * sigma n) ^ 2 = 1 := by sorry

end GaussianGLOCC
