-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_theorem_7_5
-- name    : MomentPolytopes.QuantumFunctionals.theorem_7_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:05:45.156624+00:00
-- url     : https://prove2.me/theorems/502fadc3-6da4-4851-9cc4-4c98c40e83b6
-- title:
--   Theorem 7.5 — (7.6) holds for all η ∈ (0, 1]; hence the step-size condition holds for (7.5) with η ∈ (0, 1]
-- statement:
--   For every $d$, all dimensions $n_1,\dots,n_d$, every probability distribution $\theta$ on $[d]$ and every $\eta\in(0,1]$:
--
--   1. for every positive-semidefinite $\rho$ of trace one on $\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$ with invertible marginals $\rho_\ell=\operatorname{tr}_{\check\ell}\rho$, the inequality (7.6) holds:
--   $$\eta\sum_{\ell=1}^d\theta_\ell\,H\Big(\frac{\sigma_\ell}{\operatorname{tr}\sigma}\Big)\ \ge\ \log\operatorname{tr}\sigma,\qquad\sigma=\Big(\bigotimes_\ell\rho_\ell^{-\eta\theta_\ell/2}\Big)\rho\Big(\bigotimes_\ell\rho_\ell^{-\eta\theta_\ell/2}\Big),\ \sigma_\ell=\operatorname{tr}_{\check\ell}\sigma;$$
--   2. consequently, for every $n_0$ and every nonzero concise tensor tuple $T$, the sequence (7.5) satisfies the step-size condition (6.17) for $\phi_\theta$ with scalars $c_{k+1}=e^{\eta/2}$.
--
--   This is what allows entropic tensor scaling to take the step size $\eta=1$ although the entropy is not smooth.
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: H(X) = −tr[X log X] on PSD matrices → vnEntropy X = Shannon entropy of the sorted spectrum (natural log, 0 log 0 = 0); reason: same value on PSD matrices
--   - encoding: the step-size condition (6.17) for the sequence (7.5) → StepSizeCondition (phiTheta θ) η (entropicScalingSeq η θ T) with c_{k+1} = e^{η/2}; reason: (7.5) is (6.34) for ϕ_θ with c_{k+1} = e^{η/2} (p. 55); c_0 does not enter (6.17)
--   - encoding: 'the step-size condition (6.17) holds' for the sequence (7.5) → for every n_0 and every nonzero concise T; reason: (7.5) is defined for concise T ≠ 0 (pp. 54–55)
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 56, Theorem 7.5

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra
import Definitions.Def_MomentPolytopes_QuantumFunctionals_TensorAction
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntanglementPolytope
import Definitions.Def_MomentPolytopes_QuantumFunctionals_QuantumFunctional
import Definitions.Def_MomentPolytopes_QuantumFunctionals_MirrorDescent
import Definitions.Def_MomentPolytopes_QuantumFunctionals_EntropicScaling

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Theorem 7.5 (p. 56): (7.6) holds for all `η ∈ (0, 1]`; consequently the step-size
condition (6.17) holds for the sequence (7.5) (objective `ϕ_θ`, scalars `c_{k+1} = e^{η/2}`)
for all `η ∈ (0, 1]` and every nonzero concise tensor tuple. -/
theorem theorem_7_5 :
    (∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η → η ≤ 1 →
      ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 η θ ρ) ∧
    (∀ (d n0 : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η → η ≤ 1 →
      ∀ T : Ten d n0 n, T ≠ 0 → IsConcise T →
        StepSizeCondition (phiTheta θ) η (entropicScalingSeq η θ T)
          (fun _ => ((Real.exp (η / 2) : ℝ) : ℂ))) := by sorry

end MomentPolytopes.QuantumFunctionals
