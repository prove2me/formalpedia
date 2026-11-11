-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_theorem_7
-- name    : GainShareOpt.StochBalance.theorem_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:36.076284+00:00
-- url     : https://prove2.me/theorems/a834fcbc-485a-466f-9265-9b441d23e05a
-- title:
--   Theorem 7 — existence, flatness and regularity of optimal solutions of Program (31)
-- statement:
--   The supremal value $\gamma^*$ of Program (31) is attained. For every optimal solution $(\gamma^*,f^*)$, with $\tau^*=\tau(f^*)$,
--   $$\Phi_1(f^*)=\gamma^*,\qquad \Psi_{f^*}(\sigma)=\gamma^*\ \ (\sigma\in[0,\tau^*]). \tag{32–33}$$
--   Moreover $0<\tau^*<1$ and $f^*(\tau^*)=1-1/e$; the restriction of $f^*$ to $[0,\tau^*]$ is $C^1([0,\tau^*])$ (one-sided derivatives at the endpoints) and strictly increasing, with $1-f^*(z)<e^{-z}$ for $0\le z\le\tau^*$. All optimal solutions have the same critical interval and coincide on it.
--
--   It is the structural input to Theorem 6 and to the localization of $\gamma^*$.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: optimal solution (γ*, f*) → f with Feasible31 γ* f; reason: an optimal solution is a feasible pair at the supremal value
--   - encoding: Ψ_{f*}(σ) is the minimized value Ψ_{f*,σ}(ℓ(σ)) of (29) → psiMin f σ = min over ℓ ∈ [0, σ] of Ψ_{f,σ}(ℓ); reason: (29) defines Ψ_f(σ) as that minimum; Lemma 3 identifies the minimizer
--   - encoding: restriction to [0, τ*] belongs to C¹([0, τ*]) with one-sided endpoint derivatives → ContDiffOn ℝ 1 f (Icc 0 τ*); reason: ContDiffOn on a closed interval uses derivatives within it
--   - encoding: all optimal solutions have the same critical interval and coincide there → for any two optimal f₁, f₂: τ(f₁) = τ(f₂) and f₁ = f₂ on [0, τ(f₁)]; reason: literal
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 17, Theorem 7, (32)–(33) (proof App. J, pp. 49–56)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Theorem 7 (existence, flatness, and regularity of optimal solutions of Program (31)). -/
theorem theorem_7 :
    (∃ f : ℝ → ℝ, Feasible31 gammaStar f) ∧
    (∀ f : ℝ → ℝ, Feasible31 gammaStar f →
      Phi1 f = gammaStar ∧
      (∀ σ ∈ Set.Icc 0 (critTime f), psiMin f σ = gammaStar) ∧
      0 < critTime f ∧ critTime f < 1 ∧ f (critTime f) = 1 - Real.exp (-1) ∧
      ContDiffOn ℝ 1 f (Set.Icc 0 (critTime f)) ∧
      StrictMonoOn f (Set.Icc 0 (critTime f)) ∧
      ∀ z ∈ Set.Icc 0 (critTime f), 1 - f z < Real.exp (-z)) ∧
    (∀ f₁ f₂ : ℝ → ℝ, Feasible31 gammaStar f₁ → Feasible31 gammaStar f₂ →
      critTime f₁ = critTime f₂ ∧ ∀ z ∈ Set.Icc 0 (critTime f₁), f₁ z = f₂ z) := by sorry

end GainShareOpt.StochBalance
