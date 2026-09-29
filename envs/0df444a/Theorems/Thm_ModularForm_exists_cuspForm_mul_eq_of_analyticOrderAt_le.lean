-- Prove2me | Theorems.Thm_ModularForm_exists_cuspForm_mul_eq_of_analyticOrderAt_le
-- name    : ModularForm.exists_cuspForm_mul_eq_of_analyticOrderAt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/845d9969-50b1-5115-b4d6-72ca22e7ace9
-- title:
--   Division of modular forms: Φ/Ψ is a cusp form
-- statement:
--   Let $N$ be a natural number and let $a,b,c$ be integers with $b+c=a$. Let $\Phi$ be a modular form of weight $a$ for $\Gamma_0(N)$ and let $\Psi$ be a nonzero modular form of weight $b$ for $\Gamma_0(N)$. Assume two hypotheses. First, at every point $\tau$ of the upper half-plane the analytic order of vanishing at $\tau \in \mathbb{C}$ of $\Psi$, viewed as the function on $\mathbb{C}$ obtained by precomposing with `UpperHalfPlane.ofComplex`, is at most the analytic order of vanishing at $\tau$ of $\Phi$ viewed the same way (orders taken in $\mathbb{N}\cup\{\infty\}$). Second, for every $A \in \mathrm{SL}_2(\mathbb{Z})$ and every real $\varepsilon > 0$ one has $\|(\Phi \mid_a A)(\tau)\| \le \varepsilon\,\|(\Psi \mid_b A)(\tau)\|$ for all $\tau$ in the filter $\mathrm{atImInfty}$, where $\mid_k$ denotes the weight-$k$ slash action of $A$ regarded in $\mathrm{GL}_2(\mathbb{R})$; that is, $\Phi \mid_a A = o(\Psi \mid_b A)$ as $\operatorname{Im}\tau \to \infty$. The conclusion is that there exists a cusp form $f$ of weight $c$ for $\Gamma_0(N)$ with $f(\tau)\,\Psi(\tau) = \Phi(\tau)$ for every $\tau$ in the upper half-plane.
--
--   This is the division lemma in the graded ring of modular forms: the pointwise order condition makes the quotient $\Phi/\Psi$ holomorphic on the upper half-plane, and the decay condition along all $\mathrm{SL}_2(\mathbb{Z})$-translates makes it vanish at every cusp, so that the quotient is a cusp form of the difference weight. It is used to produce cusp forms from quotients of explicit modular forms by theta series, in [`ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_of_isIntegral`](thm.html#ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_of_isIntegral) and [`ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral`](thm.html#ModularCurve.exists_cuspForm_qExpansion_eq_mul_thetaL_pow_of_isIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_cuspForm_mul_eq_of_analyticOrderAt_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_cuspForm_mul_eq_of_analyticOrderAt_le (N : ℕ) {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (CongruenceSubgroup.Gamma0 N) a) (Ψ : ModularForm (CongruenceSubgroup.Gamma0 N) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ), 0 < ε →
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ ε * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : CuspForm (CongruenceSubgroup.Gamma0 N) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by sorry
