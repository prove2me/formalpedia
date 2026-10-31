-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_188
-- name    : FuchsThesis.Holevo.eq_3_188
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:28.656314+00:00
-- url     : https://prove2.me/theorems/04f79b58-07a1-4877-b0f0-52cf59f59469
-- title:
--   Eq. (3.188): $\sum\Phi(\lambda_j,\lambda_k)|\Delta_{jk}|^2\ge\sum\frac{2}{\lambda_j+\lambda_k}|\Delta_{jk}|^2$, i.e. $S''\le L''$
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional space and $0<t<1$. Let $\lambda_j$ and $|j\rangle$ be the eigenvalues and an orthonormal eigenbasis of $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$, and $\Delta_{jk}=\langle j|\hat\rho_1-\hat\rho_0|k\rangle$. Then
--
--   $$
--   \sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \Phi(\lambda_j,\lambda_k)\,|\Delta_{jk}|^2 \;\ge\; \sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \frac{2}{\lambda_j+\lambda_k}\,|\Delta_{jk}|^2 .
--   $$
--
--   By (3.160) and (3.183) this is the inequality $S''(t)\le L''(t)$ of (3.165).
--
--   **Formalization Note** Pairs with $\lambda_j=0<\lambda_k$, where Lean's closed form of $\Phi$ is a finite junk value, have $\Delta_{jk}=0$ for $0<t<1$.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - reading: the comparison S″(t) ≤ L″(t) at the channel parameter t → t ∈ (0, 1); reason: the functions are defined on [0, 1] only, so a second derivative is two-sided only inside; at t ∈ {0, 1} the value can be infinite (ρ0 = |0⟩⟨0|, ρ1 = 1/2 on a qubit: an eigenvalue of ρ is t/2 with Δ-component 1/2, so the term is 1/(2t) → ∞), and the source's derivation of (3.179)–(3.183) assumes 0 < t < 1
--   - encoding: an eigenbasis |j⟩ of ρ̂ → the columns of Mathlib's eigenvectorUnitary of ρ̂; reason: both sums are independent of the choice
--   - encoding: Φ(λ_j, λ_k) = +∞ for a pair with λ_j = 0 < λ_k → Lean's phi is finite there (Real.log 0 = 0); reason: for 0 < t < 1 every such pair has Δ_jk = 0 (3.179), so its term is 0 either way and no instance changes
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.188), p.71 (PDF p.80)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_eigval
import Definitions.Def_FuchsThesis_Holevo_eigCoord
import Definitions.Def_FuchsThesis_Holevo_phi

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.188), p.71 (PDF p.80): for density operators
`ρ̂0, ρ̂1` and `0 < t < 1` (so that `S″(t) ≤ L″(t)`),
`∑_{j,k | λ_j + λ_k ≠ 0} Φ(λ_j, λ_k) |Δ_jk|² ≥ ∑_{j,k | λ_j + λ_k ≠ 0} (2/(λ_j + λ_k)) |Δ_jk|²`,
with `λ_j`, `|j⟩` the eigenvalues and an eigenbasis of `ρ̂ = (1 − t)ρ̂0 + tρ̂1` and
`Δ_jk = ⟨j|ρ̂1 − ρ̂0|k⟩`.

**Formalization Note.** `Φ` is `phi`. For `0 < t < 1` the pairs with `λ_j = 0 < λ_k`, where
Lean's `phi` is a finite junk value, have `Δ_jk = 0` (3.179); the hypothesis `0 < t < 1` is the
range on which the source takes second derivatives (pp.67–71). -/
theorem eq_3_188 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    (∑ j, ∑ k,
      if eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k ≠ 0 then
        2 / (eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k) *
          ‖eigCoord (mixState ρ0 ρ1 t) (ρ1 - ρ0) j k‖ ^ 2
      else 0) ≤
    ∑ j, ∑ k,
      if eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k ≠ 0 then
        phi (eigval (mixState ρ0 ρ1 t) j) (eigval (mixState ρ0 ρ1 t) k) *
          ‖eigCoord (mixState ρ0 ρ1 t) (ρ1 - ρ0) j k‖ ^ 2
      else 0 := by sorry

end FuchsThesis.Holevo
