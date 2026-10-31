-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_183
-- name    : FuchsThesis.Holevo.eq_3_183
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:50.684924+00:00
-- url     : https://prove2.me/theorems/25cad0b2-a709-4afd-9bc8-595002f8fdcc
-- title:
--   Eq. (3.183): $J''(t)\ge-\mathrm{tr}(\hat\Delta\mathcal L_{\hat\rho}(\hat\Delta))=-\sum\frac{2}{\lambda_j+\lambda_k}|\Delta_{jk}|^2$ for every measurement
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional space, $\{\hat E_b\}$ a POVM with finitely many outcomes, and $0<t<1$. With $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$ (eigenvalues $\lambda_j$, eigenbasis $|j\rangle$), $\hat\Delta=\hat\rho_1-\hat\rho_0$, $\Delta_{jk}=\langle j|\hat\Delta|k\rangle$ and $\mathcal L_{\hat\rho}$ the super-operator (3.181), the second derivative of the mutual information (3.144) satisfies
--
--   $$
--   J''(t) \;\ge\; -\mathrm{tr}\big(\mathcal L_{\hat\rho}(\hat\Delta)\,\hat\rho\,\mathcal L_{\hat\rho}(\hat\Delta)\big) \;=\; -\mathrm{tr}\big(\hat\Delta\,\mathcal L_{\hat\rho}(\hat\Delta)\big) \;=\; -\sum_{\{j,k\,|\,\lambda_j+\lambda_k\ne0\}} \frac{2}{\lambda_j+\lambda_k}\,|\Delta_{jk}|^2 .
--   $$
--
--   The right-hand side, which does not depend on the measurement, is $L''(t)$ of (3.187); this is the inequality $L''(t)\le J''(t)$ of (3.165).
--
--   **Formalization Note** The inequality compares real numbers (real part of the first trace); the two equalities are stated in $\mathbb C$ and so also assert that the traces are real.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - encoding: a measurement {Ê_b} with finitely many outcomes → a family E : Fin m → Matrix d d ℂ for any m, with FuchsVdGraaf.IsPOVM E; reason: Lean convention; the same measurements
--   - reading: J″(t) at the channel parameter t → t ∈ (0, 1); reason: the functions are defined on [0, 1] only, so a second derivative is two-sided only inside; at t ∈ {0, 1} the value can be infinite (ρ0 = |0⟩⟨0|, ρ1 = 1/2 on a qubit: an eigenvalue of ρ is t/2 with Δ-component 1/2, so the term is 1/(2t) → ∞), and the source's derivation of (3.179)–(3.183) assumes 0 < t < 1
--   - encoding: J″(t) → deriv (deriv J) t; reason: J is twice differentiable on (0, 1) (eq. (3.156)), so this is the second derivative
--   - encoding: an eigenbasis |j⟩ of ρ̂ → the columns of Mathlib's eigenvectorUnitary of ρ̂; reason: the sum is independent of the choice
--   - encoding: traces as complex numbers → the inequality compares −Re tr(𝓛_ρ̂(Δ̂)ρ̂𝓛_ρ̂(Δ̂)) with J″(t), and the two equalities are stated in ℂ (the last with the real sum cast to ℂ); reason: both traces are real for 0 < t < 1, so this is the source's chain
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.183), p.70 (PDF p.79)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_mutualInfo
import Definitions.Def_FuchsThesis_Holevo_eigval
import Definitions.Def_FuchsThesis_Holevo_eigCoord
import Definitions.Def_FuchsThesis_Holevo_lyapInv

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.183), p.70 (PDF p.79): for density operators
`ρ̂0, ρ̂1`, every POVM `{Ê_b}` and `0 < t < 1`,
`J″(t) ≥ −tr(𝓛_ρ̂(Δ̂) ρ̂ 𝓛_ρ̂(Δ̂)) = −tr(Δ̂ 𝓛_ρ̂(Δ̂)) = −∑_{j,k | λ_j + λ_k ≠ 0} (2/(λ_j + λ_k)) |Δ_jk|²`,
with `ρ̂ = (1 − t)ρ̂0 + tρ̂1`, `Δ̂ = ρ̂1 − ρ̂0`, `λ_j`, `|j⟩` eigenvalues and eigenbasis of `ρ̂`.

**Formalization Note.** `J″(t)` is `deriv (deriv J) t`; `J` is twice differentiable on `(0, 1)`
(eq. (3.156)), so this is the true second derivative. The inequality compares real parts; the two
equalities are stated in `ℂ`, which also says that both traces are real. -/
theorem eq_3_183 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix d d ℂ) (hE : FuchsVdGraaf.IsPOVM E) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    -(Matrix.trace (lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0) * mixState ρ0 ρ1 t *
          lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0))).re ≤
        deriv (deriv (fun s => mutualInfo ρ0 ρ1 E s)) t ∧
      Matrix.trace (lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0) * mixState ρ0 ρ1 t *
          lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0)) =
        Matrix.trace ((ρ1 - ρ0) * lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0)) ∧
      Matrix.trace ((ρ1 - ρ0) * lyapInv (mixState ρ0 ρ1 t) (ρ1 - ρ0)) =
        ((∑ j, ∑ k,
          if eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k ≠ 0 then
            2 / (eigval (mixState ρ0 ρ1 t) j + eigval (mixState ρ0 ρ1 t) k) *
              ‖eigCoord (mixState ρ0 ρ1 t) (ρ1 - ρ0) j k‖ ^ 2
          else 0 : ℝ) : ℂ) := by sorry

end FuchsThesis.Holevo
