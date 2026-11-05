-- Prove2me | Theorems.Thm_MultiParamQEC_eq_12_14_naimark_vectors
-- name    : MultiParamQEC.eq_12_14_naimark_vectors
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:59.589088+00:00
-- url     : https://prove2.me/theorems/c8cd358b-2628-47a5-8ad6-bca2326c60f6
-- title:
--   Eqs. (12)–(14) — every measurement gives Matsumoto-feasible vectors with Gram matrix $\Sigma$
-- statement:
--   Let $\omega\mapsto|\psi_\omega\rangle$, $\omega\in\mathbb R^P$, be a family of unit vectors in $\mathcal H=\mathbb C^n$, differentiable at $\omega_0$, write $|\psi\rangle=|\psi_{\omega_0}\rangle$ and $\partial_j|\psi\rangle$ for its partial derivatives at $\omega_0$. For every POVM $\{M_\ell\}$ on $\mathcal H$ and every estimator $\tilde{\boldsymbol\omega}$ locally unbiased at $\omega_0$ there are vectors
--   $$|x_1\rangle,\dots,|x_P\rangle\in\mathrm{span}\{|\psi\rangle,\partial_1|\psi\rangle,\dots,\partial_P|\psi\rangle\}\oplus\mathbb C^P$$
--   satisfying the constraints (14), $\mathrm{Im}\langle x_i|x_j\rangle=0$, $\langle x_i|\psi\rangle=0$, $2\,\mathrm{Re}\langle x_i|\partial_j\psi\rangle=\delta_{ij}$, whose Gram matrix $\langle x_i|x_j\rangle$ equals the covariance matrix $\Sigma$ of the estimator.
--
--   This is the lower-bound half of the Matsumoto bound (11): the vectors (12), built from a Naimark dilation of the measurement, are mapped isometrically into a $(2P+1)$-dimensional space.
--
--   Differences from the source:
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: x_i ∈ span{|ψ⟩, ∂_1|ψ⟩, …, ∂_P|ψ⟩} ⊕ ℂ^P → x_i : n ⊕ Fin P → ℂ whose ℂ^n-component lies in span_ℂ{ψ, ∂_jψ}; ψ and ∂_jψ embedded as Sum.elim · 0; reason: the direct sum ℂ^n ⊕ ℂ^P written on the index type n ⊕ Fin P; same instances
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.1, p.6, Eqs. (12)–(14) and the last paragraph of p.6

import Mathlib
import Definitions.Def_MultiParamQEC_Estimation

open scoped ComplexOrder Matrix

namespace MultiParamQEC

/-- **Every measurement yields Matsumoto-feasible vectors with Gram matrix `Σ`**
(Górecki–Zhou–Jiang–Demkowicz-Dobrzański, arXiv:1901.00896v4, Eqs. (12)–(14), p.6, and the
isometric reduction to a `(2P+1)`-dimensional space at the end of p.6).

For a differentiable family of pure states `ω ↦ |ψ_ω⟩` on `ℂ^n`, every POVM `{M_ℓ}` and every
estimator `ω̃` locally unbiased at `ω₀` admit vectors
`|x_i⟩ ∈ span{|ψ_{ω₀}⟩, ∂_1|ψ_{ω₀}⟩, …, ∂_P|ψ_{ω₀}⟩} ⊕ ℂ^P` satisfying the constraints (14)
`Im⟨x_i|x_j⟩ = 0`, `⟨x_i|ψ⟩ = 0`, `2Re⟨x_i|∂_jψ⟩ = δ_ij` whose Gram matrix `⟨x_i|x_j⟩` is the
covariance matrix `Σ` of the estimator. -/
theorem eq_12_14_naimark_vectors {n : Type} [Fintype n] [DecidableEq n] {P : ℕ}
    (ψ : (Fin P → ℝ) → n → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1) (ω₀ : Fin P → ℝ)
    (hdiff : DifferentiableAt ℝ ψ ω₀) (M : ℕ → Matrix n n ℂ) (hM : ObliviousRSP.IsPOVM M)
    (est : ℕ → Fin P → ℝ)
    (hest : IsLocallyUnbiased (fun ℓ => outcomeProb M (ψ ω₀) ℓ)
      (fun ℓ i => fderiv ℝ (fun ω => outcomeProb M (ψ ω) ℓ) ω₀ (Pi.single i 1)) ω₀ est) :
    ∃ x : Fin P → (n ⊕ Fin P) → ℂ, IsMatsumotoFeasible (ψ ω₀) (partialDeriv ψ ω₀) x ∧
      gramRe x = covariance (fun ℓ => outcomeProb M (ψ ω₀) ℓ) ω₀ est := by sorry

end MultiParamQEC
