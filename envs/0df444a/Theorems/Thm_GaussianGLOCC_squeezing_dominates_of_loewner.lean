-- Prove2me | Theorems.Thm_GaussianGLOCC_squeezing_dominates_of_loewner
-- name    : GaussianGLOCC.squeezing_dominates_of_loewner
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:23:41.666433+00:00
-- url     : https://prove2.me/theorems/43053848-1748-4a4f-a2d4-9dcfeffed7e8
-- title:
--   Eq. (25) and Lemma 2: $\tilde S^Tc(r)\tilde S\ge c(r')$ implies $r\ge r'$
-- statement:
--   Let $r,r'\in\mathbb R^n$ be ascending and nonnegative, and let $\tilde S$ be a symplectic matrix with
--
--   $$
--   \tilde S^{T}c(r)\tilde S-c(r')\ \ge\ 0 .
--   $$
--
--   Then $r_k\ge r'_k$ for every $k$.
--
--   This is the step "for which by Lemma 2 it is necessary that $r\ge r'$": the symplectic spectrum is invariant under symplectic congruence, the symplectic spectrum of $c(r)$ is $(\cosh r_k)_k$, and Lemma 2 compares the spectra.
--
--   Differences from the source:
--   - encoding: s[S̃ᵀc(r)S̃] ≥ s[c(r′)] for which by Lemma 2 it is necessary that r ≥ r′ → hypothesis (S̃ᵀ c(r) S̃ − c(r′)).PosSemidef with S̃ symplectic, r and r′ ascending (Monotone) and nonnegative; conclusion ∀ k, r′ k ≤ r k; reason: the matrix inequality is the premise of (25) on the page; the vectors are ordered and nonnegative as in Theorem 1
--   - encoding: σ = ⊕ σ₁, σ₁ = [[0, −1], [1, 0]] (eq. (4)) and symplectic matrices S σ Sᵀ = σ → GaussianGLOCC.sigma n = −interleavedSymplecticForm n (the paper's σ); symplecticity is the published isSymplectic for J = −σ; reason: S σ Sᵀ = σ and S J Sᵀ = J define the same group, so no instance changes
-- source:
--   Giedke–Eisert–Cirac–Plenio, Entanglement transformations of pure Gaussian states, arXiv:quant-ph/0301038v1, eq. (25) and the following sentence, p.7

import Mathlib
import Definitions.Def_GaussianGLOCC_PhaseSpace
open QAlgorithms.Papers.Independent.Claimed50.P19 (Cov FockIndex DensityKernel GaussianWithCovariance)
open QAlgorithms.Papers.Independent.Frontier30.P08 (isSymplectic)

namespace GaussianGLOCC

/-- Giedke–Eisert–Cirac–Plenio, arXiv:quant-ph/0301038v1, eq. (25) and the following sentence,
p.7: "s[S̃ᵀc(r)S̃] ≥ s[c(r′)], (25) for which by Lemma 2 it is necessary that r ≥ r′."

Let `r`, `r′` be ascending nonnegative squeezing vectors and `S̃` a symplectic matrix with
`S̃ᵀ c(r) S̃ − c(r′)` positive semidefinite. Then `r_k ≥ r′_k` for every `k`.

**Formalization Note.** `c(r) = ⊕_k cosh(r_k)𝟙₂` (eq. (22)); both vectors ascending
(`Monotone`), as in the main theorem. -/
theorem squeezing_dominates_of_loewner {n : ℕ} (r r' : Fin n → ℝ) (hmono : Monotone r)
    (hmono' : Monotone r') (hr : ∀ k, 0 ≤ r k) (hr' : ∀ k, 0 ≤ r' k) (St : Cov n)
    (hSt : isSymplectic St) (hle : (St.transpose * cvec r * St - cvec r').PosSemidef) :
    ∀ k, r' k ≤ r k := by sorry

end GaussianGLOCC
