-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_182
-- name    : FuchsThesis.Holevo.eq_3_182
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:30.428198+00:00
-- url     : https://prove2.me/theorems/4d8e115d-dcda-422e-9f8e-c785be1cb92d
-- title:
--   Eq. (3.182): $|\mathrm{tr}(\hat\rho\hat A\mathcal L_{\hat\rho}(\hat B))|\ge\mathrm{Re}\,\mathrm{tr}(\hat\rho\hat A\mathcal L_{\hat\rho}(\hat B))=\mathrm{tr}(\hat A\hat B)$
-- statement:
--   Let $\hat\rho$ be a density operator on a finite-dimensional space, and let $\hat A$ and $\hat B$ be Hermitian operators such that $\mathcal L_{\hat\rho}(\hat B)$, given by the formula (3.181), solves the Lyapunov equation (3.177), $\tfrac12\big(\hat\rho\,\mathcal L_{\hat\rho}(\hat B)+\mathcal L_{\hat\rho}(\hat B)\,\hat\rho\big)=\hat B$. Then
--
--   $$
--   \big|\mathrm{tr}\big(\hat\rho\hat A\,\mathcal L_{\hat\rho}(\hat B)\big)\big| \;\ge\; \mathrm{Re}\big[\mathrm{tr}\big(\hat\rho\hat A\,\mathcal L_{\hat\rho}(\hat B)\big)\big] \;=\; \mathrm{tr}(\hat A\hat B) .
--   $$
--
--   This is the "lowering" property of $\mathcal L_{\hat\rho}$, which turns the Schwarz-inequality bound (3.175) on $J''(t)$ into a bound independent of the measurement.
--
--   **Formalization Note** The equality is stated in $\mathbb C$, so it also asserts that $\mathrm{tr}(\hat A\hat B)$ is real.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - reading: for Hermitian Â and B̂ → for Hermitian Â, B̂ such that 𝓛_ρ̂(B̂) solves the Lyapunov equation (3.177); reason: the last step of (3.182) uses (3.177), and the source notes (p.69) that 𝓛_ρ̂(B̂) is not well defined for a general B̂ when ρ̂ is singular; without the condition the claim is false (ρ̂ = |0⟩⟨0|, B̂ = |1⟩⟨1|, Â = 1̂: 𝓛_ρ̂(B̂) = 0 by (3.181), so the left side is 0 while tr(ÂB̂) = 1); for B̂ = Δ̂ and 0 < t < 1 the condition holds by (3.181)
--   - generalization: ρ̂ = (1 − t)ρ̂0 + tρ̂1, the mean state of the channel → ρ̂ any density operator; reason: specializes to the source's ρ̂, which is a density operator for 0 ≤ t ≤ 1
--   - encoding: |tr(·)| ≥ Re[tr(·)] = tr(ÂB̂) → the complex modulus ‖·‖ and real part in ℝ for the inequality, and Re[tr(ρ̂Â𝓛_ρ̂(B̂))] cast to ℂ equal to tr(ÂB̂) for the equality; reason: tr(ÂB̂) is real for Hermitian Â, B̂, so the equality in ℂ is the source's
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.182), p.70 (PDF p.79)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsThesis_Holevo_lyapInv

namespace FuchsThesis.Holevo

/-- Fuchs, arXiv:quant-ph/9601020v1, eq. (3.182), p.70 (PDF p.79): for a density operator `ρ̂`
and Hermitian operators `Â`, `B̂` such that `𝓛_ρ̂(B̂)` (3.181) solves the Lyapunov equation
(3.177), `½(ρ̂ 𝓛_ρ̂(B̂) + 𝓛_ρ̂(B̂) ρ̂) = B̂`,
`|tr(ρ̂ Â 𝓛_ρ̂(B̂))| ≥ Re[tr(ρ̂ Â 𝓛_ρ̂(B̂))] = tr(Â B̂)`.

**Formalization Note.** The equality is stated in `ℂ` (`Re[…]`, cast to `ℂ`, equals `tr(ÂB̂)`),
so it also says `tr(ÂB̂)` is real. The hypothesis on `B̂` is the source's: (3.182) is the check that
`𝓛_ρ̂` has the lowering property wherever `𝓛_ρ̂(B̂)` is the solution of (3.177), and the last step
of the chain uses (3.177); for `B̂ = Δ̂` and `0 < t < 1` it holds by (3.181). -/
theorem eq_3_182 {d : Type} [Fintype d] [DecidableEq d] (ρ A B : Matrix d d ℂ)
    (hρ : WildeQIT.IsDensityOperator ρ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hL : (1 / 2 : ℂ) • (ρ * lyapInv ρ B + lyapInv ρ B * ρ) = B) :
    (Matrix.trace (ρ * A * lyapInv ρ B)).re ≤ ‖Matrix.trace (ρ * A * lyapInv ρ B)‖ ∧
      (((Matrix.trace (ρ * A * lyapInv ρ B)).re : ℝ) : ℂ) = Matrix.trace (A * B) := by sorry

end FuchsThesis.Holevo
