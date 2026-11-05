-- Prove2me | Theorems.Thm_MultiParamQEC_eq_11_matsumoto_bound
-- name    : MultiParamQEC.eq_11_matsumoto_bound
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:55.840218+00:00
-- url     : https://prove2.me/theorems/eb1288e5-c598-42ff-ae9f-bf846bf514b4
-- title:
--   Eq. (11) — the Matsumoto bound is exact and saturable for pure states
-- statement:
--   Let $\omega\mapsto|\psi_\omega\rangle$, $\omega\in\mathbb R^P$, be a family of unit vectors in $\mathcal H=\mathbb C^n$, differentiable at $\omega_0$, write $|\psi\rangle=|\psi_{\omega_0}\rangle$ and $\partial_j|\psi\rangle$ for its partial derivatives at $\omega_0$, and let $W$ be a real positive definite $P\times P$ cost matrix. Then the minimum of the cost $\Delta^2_W\tilde{\boldsymbol\omega}=\mathrm{Tr}(W\Sigma)$ over all POVMs and all estimators locally unbiased at $\omega_0$ exists and equals
--   $$\min_{\{|x_i\rangle\}}\mathrm{Tr}(WV),\qquad V_{ij}=\langle x_i|x_j\rangle,$$
--   over $|x_i\rangle\in\mathrm{span}\{|\psi\rangle,\partial_1|\psi\rangle,\dots,\partial_P|\psi\rangle\}\oplus\mathbb C^P$ subject to $2\,\mathrm{Re}\langle x_i|\partial_j\psi\rangle=\delta_{ij}$, $\langle x_i|\psi\rangle=0$ and $\mathrm{Im}\,V=0$; both minima are attained. The only exception is the degenerate case in which neither program has a feasible point.
--
--   This is the Holevo–Cramér–Rao bound specialized to pure states, together with its saturability by individual measurements; it is the starting point of the proof of Theorem 2.
--
--   Differences from the source:
--   - encoding: a POVM {M_ℓ} with outcomes ℓ of unspecified cardinality, sums Σ_ℓ → POVM indexed by ℕ (ObliviousRSP.IsPOVM: PSD elements, HasSum M 1), sums as HasSum, variances summable; reason: every finite or countable POVM is such a family (pad with zero elements); the sums of (2) and (4) must converge for Σ to be defined
--   - encoding: x_i ∈ span{|ψ⟩, ∂_1|ψ⟩, …, ∂_P|ψ⟩} ⊕ ℂ^P → x_i : n ⊕ Fin P → ℂ whose ℂ^n-component lies in span_ℂ{ψ, ∂_jψ}; ψ and ∂_jψ embedded as Sum.elim · 0; reason: the direct sum ℂ^n ⊕ ℂ^P written on the index type n ⊕ Fin P; same instances
--   - reading: "min" over the cost and over the program, implicitly assuming feasibility → either both sets are empty, or both minima exist and coincide; reason: the stronger reading: no feasibility hypothesis is added, and the degenerate case is stated instead of excluded
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.1, p.6, Eq. (11) and the sentence after it

import Mathlib
import Definitions.Def_MultiParamQEC_Estimation

open scoped ComplexOrder Matrix

namespace MultiParamQEC

/-- **The Matsumoto bound, with saturability** (Górecki–Zhou–Jiang–Demkowicz-Dobrzański,
arXiv:1901.00896v4, Eq. (11), p.6, and the sentence after it: "It was also shown in [49] that the
bound is always saturable using individual measurements").

For a differentiable family of pure states `ω ↦ |ψ_ω⟩` on `ℂ^n`, a point `ω₀` and a real positive
definite cost matrix `W`, the minimum of `Δ²_W ω̃ = Tr(WΣ)` over all POVMs and estimators locally
unbiased at `ω₀` exists and equals the minimum of `Tr(WV)`, `V_ij = ⟨x_i|x_j⟩`, over
`|x_i⟩ ∈ span{|ψ_{ω₀}⟩, ∂_1|ψ_{ω₀}⟩, …, ∂_P|ψ_{ω₀}⟩} ⊕ ℂ^P` subject to
`2Re⟨x_i|∂_jψ⟩ = δ_ij`, `⟨x_i|ψ⟩ = 0`, `Im V = 0` — unless both programs are infeasible.

**Formalization Note.** "min" presupposes feasibility; the statement makes the degenerate case
explicit (both sets empty) instead of assuming it away. Both minima are attained. -/
theorem eq_11_matsumoto_bound {n : Type} [Fintype n] [DecidableEq n] {P : ℕ}
    (ψ : (Fin P → ℝ) → n → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1) (ω₀ : Fin P → ℝ)
    (hdiff : DifferentiableAt ℝ ψ ω₀) (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef) :
    (familyCostSet ψ ω₀ W = ∅ ∧ matsumotoSet (ψ ω₀) (partialDeriv ψ ω₀) W = ∅) ∨
      ∃ v : ℝ, IsLeast (matsumotoSet (ψ ω₀) (partialDeriv ψ ω₀) W) v ∧
        IsLeast (familyCostSet ψ ω₀ W) v := by sorry

end MultiParamQEC
