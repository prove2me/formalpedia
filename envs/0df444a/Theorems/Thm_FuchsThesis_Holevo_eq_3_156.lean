-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_156
-- name    : FuchsThesis.Holevo.eq_3_156
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:03.005514+00:00
-- url     : https://prove2.me/theorems/fa6134d0-3ac7-4d16-b0d4-2f82a09a0d91
-- title:
--   Eq. (3.156): $J''(t)=-\sum_b (\mathrm{tr}\,\hat\Delta\hat E_b)^2/\mathrm{tr}\,\hat\rho\hat E_b$
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional space, $\{\hat E_b\}$ a POVM with finitely many outcomes, $\hat\Delta=\hat\rho_1-\hat\rho_0$, and $\hat\rho=(1-t)\hat\rho_0+t\hat\rho_1$. For every $0<t<1$ the mutual information $J$ of (3.144) is twice differentiable at $t$, and
--
--   $$
--   J''(t) = -\sum_b \frac{\big(\mathrm{tr}(\hat\Delta\hat E_b)\big)^2}{\mathrm{tr}(\hat\rho\hat E_b)} .
--   $$
--
--   In particular $J$ is concave on $[0,1]$ for every measurement; the formula has no logarithms, which is what makes its minimization over measurements tractable.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - encoding: a measurement {Ê_b} with finitely many outcomes → a family E : Fin m → Matrix d d ℂ for any m, with FuchsVdGraaf.IsPOVM E; reason: Lean convention; the same measurements
--   - reading: J″(t) at the channel parameter t → t ∈ (0, 1); reason: the functions are defined on [0, 1] only, so a second derivative is two-sided only inside; at t ∈ {0, 1} the value can be infinite (ρ0 = |0⟩⟨0|, ρ1 = 1/2 on a qubit: an eigenvalue of ρ is t/2 with Δ-component 1/2, so the term is 1/(2t) → ∞), and the source's derivation of (3.179)–(3.183) assumes 0 < t < 1
--   - encoding: J″(t) → J differentiable at t and HasDerivAt (deriv J) (value) t; reason: the same assertion (J twice differentiable at t with that second derivative)
--   - encoding: the sum over outcomes b (terms with tr(ρ̂Ê_b) = 0 are meaningless) → the sum over all b with Lean's x/0 = 0 and traces as real parts; reason: for 0 < t < 1, tr(ρ̂Ê_b) = 0 forces tr(ρ̂0Ê_b) = tr(ρ̂1Ê_b) = 0, so the outcome contributes 0 to J and its numerator tr(Δ̂Ê_b) is 0
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.156), p.67 (PDF p.76)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsVdGraaf_outcomeDist
import Definitions.Def_FuchsThesis_Holevo_mixState
import Definitions.Def_FuchsThesis_Holevo_mutualInfo

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.156), p.67 (PDF p.76): for density operators
`ρ̂0, ρ̂1`, every POVM `{Ê_b}` and every `t ∈ (0, 1)`, the mutual information `J(t)` (3.144) is
twice differentiable at `t` and
`J″(t) = −∑_b (tr(Δ̂ Ê_b))² / tr(ρ̂ Ê_b)`, with `Δ̂ = ρ̂1 − ρ̂0` and `ρ̂ = (1 − t)ρ̂0 + tρ̂1`.

**Formalization Note.** `tr(ρ̂ Ê_b)` is the published `FuchsVdGraaf.outcomeDist`. Stated as: `J` is differentiable at `t`, and `deriv J` has derivative
equal to the right side at `t`. Traces are real parts. An outcome with `tr(ρ̂ Ê_b) = 0` at some
`t ∈ (0, 1)` has `tr(ρ̂0 Ê_b) = tr(ρ̂1 Ê_b) = 0`, so `tr(Δ̂ Ê_b) = 0`; its term is `0/0`, which
Lean evaluates to `0`, matching its zero contribution to `J`. -/
theorem eq_3_156 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix d d ℂ) (hE : FuchsVdGraaf.IsPOVM E) (t : ℝ)
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (fun s => mutualInfo ρ0 ρ1 E s) t ∧
      HasDerivAt (deriv (fun s => mutualInfo ρ0 ρ1 E s))
        (-∑ b, (Matrix.trace ((ρ1 - ρ0) * E b)).re ^ 2 /
          FuchsVdGraaf.outcomeDist (mixState ρ0 ρ1 t) E b)
        t := by sorry

end FuchsThesis.Holevo
