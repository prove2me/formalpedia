-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_lemma_7_4
-- name    : MomentPolytopes.QuantumFunctionals.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:06:07.801206+00:00
-- url     : https://prove2.me/theorems/106efc75-b379-4def-89d8-024c1897b047
-- title:
--   Lemma 7.4 — the step-size condition for (7.5) reduces to the entropy inequality (7.6); η = 1 suffices; at η = 1, (7.6) ⇔ Σ θ_ℓ H(σ_ℓ) ≥ 0
-- statement:
--   Let $\theta$ be a probability distribution on $[d]$, $\eta>0$, and for a positive-semidefinite $\rho$ of trace one on $\mathbb C^{n_1}\otimes\dots\otimes\mathbb C^{n_d}$ whose marginals $\rho_\ell=\operatorname{tr}_{\check\ell}\rho$ are all invertible put $\sigma=(\bigotimes_\ell\rho_\ell^{-\eta\theta_\ell/2})\rho(\bigotimes_\ell\rho_\ell^{-\eta\theta_\ell/2})$ and $\sigma_\ell=\operatorname{tr}_{\check\ell}\sigma$. Consider the inequality
--   $$\eta\sum_{\ell=1}^d\theta_\ell\,H\Big(\frac{\sigma_\ell}{\operatorname{tr}\sigma}\Big)\ \ge\ \log\operatorname{tr}\sigma .\tag{7.6}$$
--   Then:
--
--   1. For fixed $d$, $n_1,\dots,n_d$, $\theta$ and $\eta>0$: if (7.6) holds for all such $\rho$, then for every $n_0$ and every nonzero concise tensor tuple $T\in\mathrm{Ten}(n_0;n_1,\dots,n_d)$ the sequence (7.5), $T_{k+1}=(I\otimes\bigotimes_\ell\rho_\ell^{-\eta\theta_\ell/2})T_k$, $(\rho_1,\dots,\rho_d)=\mu(T_k)$, $T_0=T$, satisfies the step-size condition (6.17) for $\phi_\theta$ with scalars $c_{k+1}=e^{\eta/2}$.
--   2. If (7.6) holds at $\eta=1$ for all $d$, all dimensions $n_1,\dots,n_d$, all probability distributions $\theta$ and all such $\rho$, then it holds for all $\eta\in(0,1]$ (for all $d$, dimensions, $\theta$, $\rho$).
--   3. At $\eta=1$, (7.6) is equivalent to $\sum_{\ell=1}^d\theta_\ell H(\sigma_\ell)\ge0$.
--
--   This lemma turns the step-size condition of Hadamard mirror descent for $\phi_\theta$ into a quantum entropy inequality, which Theorem 7.5 then proves. Here $H$ is the von Neumann entropy of a PSD matrix of any trace (the $\sigma_\ell$ need not have trace one).
--
--   Differences from the source:
--   - encoding: ℓ ∈ [d] = {1, …, d} → ℓ : Fin d (0-based); reason: indexing convention; same instances
--   - encoding: H(X) = −tr[X log X] on PSD matrices → vnEntropy X = Shannon entropy of the sorted spectrum (natural log, 0 log 0 = 0); reason: same value on PSD matrices
--   - encoding: the step-size condition (6.17) for the sequence (7.5) → StepSizeCondition (phiTheta θ) η (entropicScalingSeq η θ T) with c_{k+1} = e^{η/2}; reason: (7.5) is (6.34) for ϕ_θ with c_{k+1} = e^{η/2} (p. 55); c_0 does not enter (6.17)
--   - encoding: step size η (Definition 5.1, p. 24: η > 0) in the first claim → hypothesis 0 < η; reason: the standing assumption on the step size made explicit
--   - encoding: 'it suffices to prove …' (twice) → implications: (∀ ρ, (7.6)) → step-size condition for every nonzero concise T and every n_0; (∀ d n θ ρ, (7.6) at η = 1) → (∀ d n θ, ∀ η ∈ (0, 1], ∀ ρ, (7.6)); reason: the logical content of the two reductions as printed
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 55, Lemma 7.4

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

/-- Lemma 7.4 (p. 55), all three claims:
(i) for fixed `d`, `n`, `θ` and `η > 0`, the inequality (7.6) for every trace-one PSD `ρ` with
invertible marginals implies the step-size condition (6.17) for the sequence (7.5)
(scalars `c_{k+1} = e^{η/2}`, objective `ϕ_θ`) for every nonzero concise tensor tuple;
(ii) (7.6) at `η = 1` for all `d`, dimensions and `θ` implies (7.6) for all `η ∈ (0, 1]`;
(iii) at `η = 1`, (7.6) is equivalent to `∑_ℓ θ_ℓ H(σ_ℓ) ≥ 0`. -/
theorem lemma_7_4 :
    (∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η →
      (∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 η θ ρ) →
      ∀ (n0 : ℕ) (T : Ten d n0 n), T ≠ 0 → IsConcise T →
        StepSizeCondition (phiTheta θ) η (entropicScalingSeq η θ T)
          (fun _ => ((Real.exp (η / 2) : ℝ) : ℂ))) ∧
    ((∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
        ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 1 θ ρ) →
      ∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ) (η : ℝ), IsProbVec θ → 0 < η → η ≤ 1 →
        ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
          (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) → EntropyIneq76 η θ ρ) ∧
    (∀ (d : ℕ) (n : Fin d → ℕ) (θ : Fin d → ℝ), IsProbVec θ →
      ∀ ρ : Matrix (MIdx n) (MIdx n) ℂ, ρ.PosSemidef → ρ.trace = 1 →
        (∀ ℓ, (partialTrace ℓ ρ).det ≠ 0) →
          (EntropyIneq76 1 θ ρ ↔
            0 ≤ ∑ ℓ, θ ℓ * vnEntropy (partialTrace ℓ (sigmaOf 1 θ ρ)))) := by sorry

end MomentPolytopes.QuantumFunctionals
