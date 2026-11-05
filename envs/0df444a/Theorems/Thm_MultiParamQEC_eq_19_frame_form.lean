-- Prove2me | Theorems.Thm_MultiParamQEC_eq_19_frame_form
-- name    : MultiParamQEC.eq_19_frame_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:37:56.671904+00:00
-- url     : https://prove2.me/theorems/9ba000c1-7755-4087-ace7-d475ce1d02da
-- title:
--   Eq. (19) — orthonormal-frame form of the Matsumoto bound (corrected: frames orthogonal to $|\psi\rangle$)
-- statement:
--   Let $\omega\mapsto|\psi_\omega\rangle$, $\omega\in\mathbb R^P$, be a family of unit vectors in $\mathcal H=\mathbb C^n$, differentiable at $\omega_0$, write $|\psi\rangle=|\psi_{\omega_0}\rangle$ and $\partial_j|\psi\rangle$ for its partial derivatives at $\omega_0$, let $W$ be real positive definite, and assume $\dim\mathcal H\ge2P+1$. Then the minimum of the Matsumoto program (11) equals
--   $$\min_{|c_1\rangle,\dots,|c_P\rangle\in\mathcal H}\mathrm{Tr}\big(W(D^TD)^{-1}\big),\qquad D_{ij}=2\,\mathrm{Re}\langle c_i|\partial_j\psi\rangle,$$
--   subject to $\langle c_i|c_j\rangle=\delta_{ij}$, $\langle c_i|\psi\rangle=0$ and $D$ invertible; both minima are attained, unless neither program is feasible.
--
--   This reformulation, with the $c_i$ an orthonormal frame of the optimal $x_i$, is the form that is later turned into a semidefinite program.
--
--   Differences from the source:
--   - correction: (19): minimum over orthonormal |c_1⟩, …, |c_P⟩ ∈ H subject only to ⟨c_i|c_j⟩ = δ_ij → the frame is also required orthogonal to |ψ⟩ (⟨c_i|ψ⟩ = 0); reason: the printed (19) is false: H = ℂ³, ψ = e₀, ∂ψ = i e₀ + e₁, P = 1, W = 1 gives Matsumoto minimum 1/4, but c = ∂ψ/√2 gives D⁻² = 1/8; in the text the c_i are an orthonormal basis of span{x_i} and each x_i ⊥ ψ by (14)
--   - encoding: x_i ∈ span{|ψ⟩, ∂_1|ψ⟩, …, ∂_P|ψ⟩} ⊕ ℂ^P → x_i : n ⊕ Fin P → ℂ whose ℂ^n-component lies in span_ℂ{ψ, ∂_jψ}; ψ and ∂_jψ embedded as Sum.elim · 0; reason: the direct sum ℂ^n ⊕ ℂ^P written on the index type n ⊕ Fin P; same instances
--   - encoding: (DᵀD)⁻¹ in the objective → D required invertible ((det D) ≠ 0); reason: the inverse is only defined for invertible D; this excludes Mathlib's junk value 0 and no instance of the source
--   - reading: "min" over the cost and over the program, implicitly assuming feasibility → either both sets are empty, or both minima exist and coincide; reason: the stronger reading: no feasibility hypothesis is added, and the degenerate case is stated instead of excluded
-- source:
--   Górecki–Zhou–Jiang–Demkowicz-Dobrzański, Optimal probes and error-correction schemes in multi-parameter quantum metrology, arXiv:1901.00896v4, Sec. 4.2.1, p.7, Eqs. (18)–(19)

import Mathlib
import Definitions.Def_MultiParamQEC_Estimation

open scoped ComplexOrder Matrix

namespace MultiParamQEC

/-- **Orthonormal-frame form of the Matsumoto bound** (corrected: frames orthogonal to `ψ`)
(Górecki–Zhou–Jiang–Demkowicz-Dobrzański, arXiv:1901.00896v4, Eqs. (18)–(19), p.7).

If `dim H ≥ 2P + 1`, then for a differentiable family of pure states on `H = ℂ^n` at `ω₀` the
minimum of the Matsumoto program (11) equals the minimum of `Tr(W(DᵀD)⁻¹)`,
`D_ij = 2Re⟨c_i|∂_jψ⟩`, over orthonormal `c_1, …, c_P ∈ H` with `⟨c_i|ψ⟩ = 0` and `D` invertible —
unless both programs are infeasible.

**Formalization Note.** The printed (19) imposes only `⟨c_i|c_j⟩ = δ_ij`; without `⟨c_i|ψ⟩ = 0`
it is false (for `H = ℂ³`, `ψ = e₀`, `∂ψ = i e₀ + e₁`, `P = 1`, `W = 1`, the Matsumoto minimum is
`1/4` but `c = ∂ψ/√2` gives `D⁻² = 1/8`). In the text the `c_i` are an orthonormal basis of
`span{x_i}`, and every `x_i ⊥ ψ`. -/
theorem eq_19_frame_form {n : Type} [Fintype n] [DecidableEq n] {P : ℕ}
    (hdim : 2 * P + 1 ≤ Fintype.card n)
    (ψ : (Fin P → ℝ) → n → ℂ) (hψ : ∀ ω, star (ψ ω) ⬝ᵥ ψ ω = 1) (ω₀ : Fin P → ℝ)
    (hdiff : DifferentiableAt ℝ ψ ω₀) (W : Matrix (Fin P) (Fin P) ℝ) (hW : W.PosDef) :
    (matsumotoSet (ψ ω₀) (partialDeriv ψ ω₀) W = ∅ ∧ frameSet (ψ ω₀) (partialDeriv ψ ω₀) W = ∅) ∨
      ∃ v : ℝ, IsLeast (matsumotoSet (ψ ω₀) (partialDeriv ψ ω₀) W) v ∧
        IsLeast (frameSet (ψ ω₀) (partialDeriv ψ ω₀) W) v := by sorry

end MultiParamQEC
