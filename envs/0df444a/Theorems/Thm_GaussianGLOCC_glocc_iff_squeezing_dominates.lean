-- Prove2me | Theorems.Thm_GaussianGLOCC_glocc_iff_squeezing_dominates
-- name    : GaussianGLOCC.glocc_iff_squeezing_dominates
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:59.888476+00:00
-- url     : https://prove2.me/theorems/f06a50b4-ebeb-4f54-81ea-2d21a32ae7d2
-- title:
--   Theorem 1: a pure Gaussian state can be transformed into another by Gaussian LOCC iff its squeezing vector dominates entrywise
-- statement:
--   Let $\rho$ and $\rho'$ be two pure Gaussian states of $n\times n$ modes ($A$ holds $n$ modes, $B$ holds $n$ modes) with covariance matrices $\gamma$, $\gamma'$, characterized by ascendingly ordered squeezing vectors $r$, $r'$: each covariance matrix is brought by local symplectic transformations to the normal form $\gamma_r$ (resp. $\gamma_{r'}$) of a product of two-mode squeezed states. Then $\rho$ can be transformed deterministically into $\rho'$ by Gaussian local operations with classical communication if and only if
--
--   $$
--   r\ge r',\qquad\text{i.e.}\qquad r_k\ge r'_k\ \text{ for all }k=1,\dots,n .
--   $$
--
--   Gaussian local operations with classical communication are protocols of local Gaussian unitaries, vacuum ancillas, discarding of modes and homodyne detections in either party, where later steps may depend on all earlier measurement outcomes and every outcome must yield $\rho'$.
--
--   Unlike general LOCC, where pure-state convertibility is governed by majorization of Schmidt coefficients, Gaussian LOCC is governed by the much stronger entrywise order of squeezing vectors; in particular no concentration or dilution of two-mode squeezing is possible.
--
--   Differences from the source:
--   - reading: local Gaussian operations with classical communication (GLOCC) → GLOCCReach: deterministic adaptive protocols of local Gaussian unitaries (with displacements), vacuum ancillas, discarding and ideal X-homodyne detections in either party; reason: p.2: Gaussian operations are optical elements together with homodyne measurements; p.3: concatenations of Gaussian unitaries on possibly a larger set of modes together with homodyne measurements; p.7's protocol uses exactly these steps; other ancillas and dyne detections are compositions; a homodyne step needs a continuation for every outcome y ∈ ℝ, which for Gaussian protocols is the same as for almost every y, since conditional states for different y differ by local displacements (those of B use the communicated y)
--   - encoding: characterized by ordered squeezing vectors r and r′ → IsSqueezingVector γ r: r ascending (Monotone) and nonnegative, (S_A ⊕ S_B)γ(S_A ⊕ S_B)ᵀ = normalForm r for symplectic S_A, S_B; reason: p.4: "characterized by vectors r and r′ of ascendingly ordered squeezing parameters"; by Lemma 1 this is the state-level normal form; Lemma 1 prints the descending order, and either common order gives the same comparison
--   - encoding: pure Gaussian state of n × n modes with CM γ (eqs. (1)–(2), vacuum CM 𝟙) → IsPureGaussian ρ γ on DensityKernel (n + n), A = first n modes, B = last n modes (published GaussianWithCovariance plus a norm-one vector representative); reason: the published predicate's extra clauses (γ positive definite, finite mean energy) hold for every Gaussian state; the mode order is a layout choice
--   - encoding: σ = ⊕ σ₁, σ₁ = [[0, −1], [1, 0]] (eq. (4)) and symplectic matrices S σ Sᵀ = σ → GaussianGLOCC.sigma n = −interleavedSymplecticForm n (the paper's σ); symplecticity is the published isSymplectic for J = −σ; reason: S σ Sᵀ = σ and S J Sᵀ = J define the same group, so no instance changes
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, Theorem 1, eqs. (9)–(10), p.4

import Mathlib
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_GLOCCReach
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, *Entanglement transformations of pure Gaussian states*,
arXiv:quant-ph/0301038v1, Theorem 1 (Pure-state entanglement transformations), p.4: "Let ρ and
ρ′ be two n×n pure states with CM γ and γ′, characterized by ordered squeezing vectors r and r′,
respectively. Then ρ can be transformed into ρ′ be local Gaussian operations with classical
communication iff r ≥ r′", where (9) "r ≥ r′ iff r_k ≥ r′_k for all k = 1, . . . , n".

For pure Gaussian states `ρ`, `ρ′` of `n + n` modes (A = first `n`, B = last `n`) with CMs `γ`, `γ′`
and ascending squeezing vectors `r`, `r′`: `ρ` can be transformed deterministically into `ρ′` by
Gaussian local operations and classical communication iff `r_k ≥ r′_k` for every `k`.

**Formalization Note.** GLOCC is `GLOCCReach`: deterministic, adaptive protocols built from
local Gaussian unitaries (with displacements), vacuum ancillas, discarding of modes and ideal
homodyne detections in either party, with later steps depending on earlier outcomes (pp.2–3,
p.7). "Characterized by squeezing vectors" is `IsSqueezingVector`: local symplectic equivalence
of the CM to the TMSS normal form (3)/(22), with ascending nonnegative vectors (p.4). First
moments are arbitrary; `n = 0` is allowed. -/
theorem glocc_iff_squeezing_dominates (n : ℕ) (ρ ρ' : DensityKernel (n + n)) (γ γ' : Cov (n + n))
    (hρ : IsPureGaussian ρ γ) (hρ' : IsPureGaussian ρ' γ')
    (r r' : Fin n → ℝ) (hr : IsSqueezingVector γ r) (hr' : IsSqueezingVector γ' r') :
    GLOCCReach ⟨n, n, ρ⟩ ⟨n, n, ρ'⟩ ↔ ∀ k, r' k ≤ r k := by sorry

end GaussianGLOCC
