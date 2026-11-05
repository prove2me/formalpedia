-- Prove2me | Theorems.Thm_MultiParamQEC_eq_15_17_achieving_measurement
-- name    : MultiParamQEC.eq_15_17_achieving_measurement
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:55.534473+00:00
-- url     : https://prove2.me/theorems/840b4668-ec6f-49a7-81eb-6815ae82a123
-- title:
--   Eqs. (15)–(17) — every Matsumoto-feasible family is achieved by a measurement
-- statement:
--   Let $\omega\mapsto|\psi_\omega\rangle$, $\omega\in\mathbb R^P$, be a family of unit vectors in $\mathcal H=\mathbb C^n$, differentiable at $\omega_0$, write $|\psi\rangle=|\psi_{\omega_0}\rangle$ and $\partial_j|\psi\rangle$ for its partial derivatives at $\omega_0$. For every family $|x_1\rangle,\dots,|x_P\rangle\in\mathrm{span}\{|\psi\rangle,\partial_j|\psi\rangle\}\oplus\mathbb C^P$ satisfying (14) there are a projective measurement $\{E_\ell\}_{\ell=0}^{P+1}$ on $\mathcal H\oplus\mathbb C^P$ (Hermitian, $E_\ell E_{\ell'}=\delta_{\ell\ell'}E_\ell$, $\sum_\ell E_\ell=\mathbb 1$) and an estimator $\tilde{\boldsymbol\omega}$ such that
--
--   1. $|x_i\rangle=\sum_{\ell=0}^{P+1}(\tilde\omega_i(\ell)-\omega_{0,i})E_\ell|\psi\rangle$ (Eq. (17));
--   2. the compression $M_\ell=\Pi_{\mathcal H}E_\ell\Pi_{\mathcal H}$ is a POVM on $\mathcal H$, the estimator is locally unbiased at $\omega_0$ for it, and its covariance matrix equals the Gram matrix $V_{ij}=\langle x_i|x_j\rangle$.
--
--   This is the saturability half of the Matsumoto bound (11): the projective measurement (15) with the estimator (16), compressed to $\mathcal H$, attains every feasible value.
--
--   Differences from the source:
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: x_i ∈ span{|ψ⟩, ∂_1|ψ⟩, …, ∂_P|ψ⟩} ⊕ ℂ^P → x_i : n ⊕ Fin P → ℂ whose ℂ^n-component lies in span_ℂ{ψ, ∂_jψ}; ψ and ∂_jψ embedded as Sum.elim · 0; reason: the direct sum ℂ^n ⊕ ℂ^P written on the index type n ⊕ Fin P; same instances
--   - encoding: the projective measurement (15) with outcomes ℓ = 0, …, P+1 on H ⊕ ℂ^P, compressed to H → E : ℕ → matrices on n ⊕ Fin P with E ℓ = 0 for ℓ > P+1; compression = the n × n block (submatrix Sum.inl Sum.inl); reason: the zero elements carry probability 0, and Π_H E Π_H restricted to H is the upper-left block; same measurement
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.1, p.7, Eqs. (15)–(17) and the sentence before them

import Mathlib
import Definitions.Def_MultiParamQEC_Estimation

open scoped ComplexOrder Matrix

namespace MultiParamQEC

/-- **Every Matsumoto-feasible family is achieved by a measurement**
(Górecki–Zhou–Jiang–Demkowicz-Dobrzański, arXiv:1901.00896v4, Eqs. (15)–(17), p.7: "for any set of
`|x_i⟩` satisfying Eq. (14) there exists a proper projective measurement on `H ⊕ ℂ^P` and a
locally unbiased estimator satisfying Eq. (12), and consequently there exists a corresponding
general measurement on `H`").

For a differentiable family of pure states `ω ↦ |ψ_ω⟩` on `H = ℂ^n` and vectors
`|x_i⟩ ∈ span{|ψ_{ω₀}⟩, ∂_jψ} ⊕ ℂ^P` feasible for (11)/(14), there are a projective measurement
`{E_ℓ}_{ℓ=0}^{P+1}` on `H ⊕ ℂ^P` (Hermitian, `E_ℓ E_ℓ′ = δ_ℓℓ′ E_ℓ`, `Σ_ℓ E_ℓ = 1`, `E_ℓ = 0` for
`ℓ > P + 1`, as in (15)) and an estimator such that
1. `|x_i⟩ = Σ_{ℓ=0}^{P+1} (ω̃_i(ℓ) − ω_{0,i}) E_ℓ |ψ_{ω₀}⟩` (Eq. (17));
2. the compression `M_ℓ = Π_H E_ℓ Π_H` to `H` is a POVM on `H`, the estimator is locally unbiased
   at `ω₀` for it, and its covariance matrix equals the Gram matrix `V_ij = ⟨x_i|x_j⟩`.

**Formalization Note.** `H ⊕ ℂ^P` is `ℂ^(n ⊕ Fin P)`, `|ψ⟩` is embedded as `Sum.elim ψ 0`, and the
compression to `H` is the `n × n` block `(E ℓ).submatrix Sum.inl Sum.inl`. -/
theorem eq_15_17_achieving_measurement {n : Type} [Fintype n] [DecidableEq n] {P : ℕ}
    (ψ : (Fin P → ℝ) → n → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1) (ω₀ : Fin P → ℝ)
    (hdiff : DifferentiableAt ℝ ψ ω₀) (x : Fin P → (n ⊕ Fin P) → ℂ)
    (hx : IsMatsumotoFeasible (ψ ω₀) (partialDeriv ψ ω₀) x) :
    ∃ (E : ℕ → Matrix (n ⊕ Fin P) (n ⊕ Fin P) ℂ) (est : ℕ → Fin P → ℝ),
      (∀ ℓ, (E ℓ).IsHermitian) ∧ (∀ ℓ ℓ', E ℓ * E ℓ' = if ℓ = ℓ' then E ℓ else 0) ∧
      (∀ ℓ, P + 1 < ℓ → E ℓ = 0) ∧ ∑ ℓ ∈ Finset.range (P + 2), E ℓ = 1 ∧
      (∀ i, x i = ∑ ℓ ∈ Finset.range (P + 2),
        (((est ℓ i - ω₀ i : ℝ)) : ℂ) • (E ℓ *ᵥ Sum.elim (ψ ω₀) 0)) ∧
      ObliviousRSP.IsPOVM (fun ℓ => (E ℓ).submatrix Sum.inl Sum.inl) ∧
      IsLocallyUnbiased (fun ℓ => outcomeProb (fun ℓ => (E ℓ).submatrix Sum.inl Sum.inl) (ψ ω₀) ℓ)
        (fun ℓ i => fderiv ℝ (fun ω => outcomeProb (fun ℓ => (E ℓ).submatrix Sum.inl Sum.inl)
          (ψ ω) ℓ) ω₀ (Pi.single i 1)) ω₀ est ∧
      covariance (fun ℓ => outcomeProb (fun ℓ => (E ℓ).submatrix Sum.inl Sum.inl) (ψ ω₀) ℓ)
        ω₀ est = gramRe x := by sorry

end MultiParamQEC
