-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_3
-- name    : GainShareOpt.StochBalance.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:35.664554+00:00
-- url     : https://prove2.me/theorems/90141daa-2378-47f9-9505-8964a2ef4d1f
-- title:
--   Lemma 3 — strict convexity of $\Psi_{f,\sigma}$ and the minimizer equation (27)
-- statement:
--   Let $f\in F_0$. For every $\sigma\in(0,\tau(f)]$ the function $\Psi_{f,\sigma}(\ell)=\Psi_f(\ell,\sigma-\ell)$ is strictly convex on $[0,\sigma]$. For every $\sigma\in[0,\tau(f)]$, its unique minimizer $\ell(\sigma)$ on $[0,\sigma]$ is the unique solution in $[0,\sigma]$ of
--   $$1-f(\sigma)=e^{-\ell}\bigl(1-f(\ell)\bigr). \tag{27}$$
--   In particular $\ell(0)=0$.
--
--   It identifies the minimized partial-load test $\Psi_f(\sigma)$ of (29).
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: its unique minimizer ℓ(σ) is the unique solution of (27) → there is ℓ₀ ∈ [0, σ] solving (27), every solution in [0, σ] equals ℓ₀, ℓ₀ minimizes Ψ_{f,σ} on [0, σ], and every minimizer equals ℓ₀; reason: spells out 'unique minimizer = unique root' without a named function
--   - encoding: In particular, ℓ(0) = 0 → not a separate clause: at σ = 0 the interval [0, σ] is {0}; reason: the σ = 0 instance of the second clause gives it
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 15, Lemma 3, (27)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Lemma 3: `Ψ_{f,σ}` is strictly convex on `[0, σ]` for `σ ∈ (0, τ(f)]`; for `σ ∈ [0, τ(f)]` its
unique minimizer `ℓ(σ)` is the unique solution in `[0, σ]` of (27). -/
theorem lemma_3 (f : ℝ → ℝ) (hf : f ∈ F0) :
    (∀ σ ∈ Set.Ioc 0 (critTime f), StrictConvexOn ℝ (Set.Icc 0 σ) (psiSigma f σ)) ∧
    (∀ σ ∈ Set.Icc 0 (critTime f), ∃ ℓ₀ ∈ Set.Icc 0 σ,
      1 - f σ = Real.exp (-ℓ₀) * (1 - f ℓ₀) ∧
      (∀ ℓ ∈ Set.Icc 0 σ, 1 - f σ = Real.exp (-ℓ) * (1 - f ℓ) → ℓ = ℓ₀) ∧
      (∀ ℓ ∈ Set.Icc 0 σ, psiSigma f σ ℓ₀ ≤ psiSigma f σ ℓ) ∧
      (∀ ℓ ∈ Set.Icc 0 σ, (∀ ℓ' ∈ Set.Icc 0 σ, psiSigma f σ ℓ ≤ psiSigma f σ ℓ') → ℓ = ℓ₀)) := by sorry

end GainShareOpt.StochBalance
