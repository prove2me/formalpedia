-- Prove2me | Theorems.Thm_GaussianGLOCC_one_local_necessity
-- name    : GaussianGLOCC.one_local_necessity
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:24:55.686316+00:00
-- url     : https://prove2.me/theorems/3aa6df36-5ea3-4f7b-aa02-eaad0509c86f
-- title:
--   Eq. (25): one-local reachability forces $\tilde S^Tc(r)\tilde S\ge c(r')$
-- statement:
--   Let $r,r'\in\mathbb R^n$ be nonnegative and suppose the TMSS product with squeezing vector $r$ can be transformed into the TMSS product with squeezing vector $r'$ by one-local Gaussian operations. Then there is a symplectic matrix $\tilde S$ with
--
--   $$
--   \tilde S^{T}c(r)\tilde S-c(r')\ \ge\ 0,\qquad c(r)=\bigoplus_k\cosh(r_k)\mathbb 1_2 .
--   $$
--
--   In the paper $\tilde S=\Lambda S\Lambda$, with $S$ the symplectic transformation of $B$'s unitary, and the inequality is what the positivity $\Gamma_A\ge i\sigma$ of the operation's CM (24) requires.
--
--   Differences from the source:
--   - generalization: ρ, ρ′ in the normal form of Lemma 1 with ordered squeezing vectors, one-local operations as in Lemma 3 with pure intermediate states → any nonnegative r, r′ (no ordering), any one-local protocol (OneLocalReach, mixed intermediate states allowed); reason: specializes to the paper's ordered vectors and pure protocols
--   - reading: Γ_A ≥ iσ can only hold if S̃ᵀc(r)S̃ − c(r′) ≥ 0, S̃ := ΛSΛ → ∃ symplectic S̃ with (S̃ᵀ c(r) S̃ − c(r′)).PosSemidef; reason: the conclusion the proof uses; S̃ is the transformation built from B's symplectic S
--   - encoding: σ = ⊕ σ₁, σ₁ = [[0, −1], [1, 0]] (eq. (4)) and symplectic matrices S σ Sᵀ = σ → GaussianGLOCC.sigma n = −interleavedSymplecticForm n (the paper's σ); symplecticity is the published isSymplectic for J = −σ; reason: S σ Sᵀ = σ and S J Sᵀ = J define the same group, so no instance changes
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, eqs. (23)–(25), p.7

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
import Definitions.Def_GaussianGLOCC_SqueezedStates
import Definitions.Def_GaussianGLOCC_GLOCCReach
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, eqs. (23)–(25), p.7: "From the
expressions for Γ₁A and Γ₂A one finds that Γ_A ≥ iσ can only hold if S̃ᵀc(r)S̃ − c(r′) ≥ 0,
meaning that s[S̃ᵀc(r)S̃] ≥ s[c(r′)], (25)" where "S̃ is the symplectic transformation S̃ := ΛSΛ".

If the TMSS product with squeezing vector `r ≥ 0` can be transformed into the TMSS product with
squeezing vector `r′ ≥ 0` by one-local Gaussian operations, then there is a symplectic `S̃` with
`S̃ᵀ c(r) S̃ − c(r′)` positive semidefinite (`c(r) = ⊕_k cosh(r_k)𝟙₂`, eq. (22)).

**Formalization Note.** No ordering of `r`, `r′` is assumed (the paper's are ordered); the
conclusion is the matrix inequality of (25), not its spectral form, which M10 converts.
`isSymplectic` is the published predicate (same group for `±σ`). -/
theorem one_local_necessity {n : ℕ} (r r' : Fin n → ℝ) (hr : ∀ k, 0 ≤ r k) (hr' : ∀ k, 0 ≤ r' k)
    (h : OneLocalReach ⟨n, n, tmssProduct r⟩ ⟨n, n, tmssProduct r'⟩) :
    ∃ St : Cov n, isSymplectic St ∧ (St.transpose * cvec r * St - cvec r').PosSemidef := by sorry

end GaussianGLOCC
