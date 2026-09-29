-- Prove2me | Theorems.Thm_ModularForm_exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le
-- name    : ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/28b61954-e688-59bf-addb-e166fb29b2e5
-- title:
--   Division of modular forms: Φ/Ψ is a cusp form
-- statement:
--   Let $\Gamma$ be an arbitrary subgroup of $\mathrm{SL}_2(\mathbb{Z})$, viewed through the canonical map as a subgroup of $\mathrm{GL}_2(\mathbb{R})$, and let $a,b,c$ be integers with $b+c=a$. Let $\Phi$ be a modular form of weight $a$ and $\Psi$ a nonzero modular form of weight $b$, both for $\Gamma$. Assume: (i) for every $\tau$ in the upper half-plane, the analytic order of vanishing at the point $\tau\in\mathbb{C}$ of the function $\Psi\circ\mathrm{ofComplex}$ is at most that of $\Phi\circ\mathrm{ofComplex}$, where $\mathrm{ofComplex}$ is the retraction of $\mathbb{C}$ onto the upper half-plane and orders are taken in $\mathbb{N}\cup\{\infty\}$; (ii) for every $A\in\mathrm{SL}_2(\mathbb{Z})$ and every real $\varepsilon>0$ one has $\|(\Phi\mid_a A)(\tau)\|\le \varepsilon\,\|(\Psi\mid_b A)(\tau)\|$ for all $\tau$ in some neighbourhood of the filter $\mathrm{Im}\,\tau\to\infty$, the bars denoting the weight-$a$ and weight-$b$ slash actions. The conclusion is that there exists a cusp form $f$ of weight $c$ for $\Gamma$ with $f(\tau)\Psi(\tau)=\Phi(\tau)$ for every $\tau$ in the upper half-plane.
--
--   This is the division lemma in the graded ring of modular forms, in a form valid for an arbitrary subgroup $\Gamma$ of $\mathrm{SL}_2(\mathbb{Z})$ (no finite-index or congruence assumption): the pointwise order condition removes the singularities of $\Phi/\Psi$ on the upper half-plane, and the $o(\Psi)$ bound at every $\mathrm{SL}_2(\mathbb{Z})$-translate of $\infty$ forces vanishing at all cusps. It is used to produce cusp forms from integrality of $q$-expansions in the construction of cusp forms as multiples of powers of a theta series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups ModularForm

theorem ModularForm.exists_cuspForm_mul_eq_of_forall_analyticOrderAt_le
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) {a b : ℤ} (c : ℤ) (habc : b + c = a)
    (Φ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) a) (Ψ : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) b) (hΨ : Ψ ≠ 0)
    (hord : ∀ τ : UpperHalfPlane, analyticOrderAt ((Ψ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ) ≤
      analyticOrderAt ((Φ : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (τ : ℂ))
    (hcusp : ∀ (A : Matrix.SpecialLinearGroup (Fin 2) ℤ) (ε : ℝ), 0 < ε →
      ∀ᶠ τ : UpperHalfPlane in UpperHalfPlane.atImInfty,
        ‖((Φ : UpperHalfPlane → ℂ) ∣[a] (A : GL (Fin 2) ℝ)) τ‖ ≤ ε * ‖((Ψ : UpperHalfPlane → ℂ) ∣[b] (A : GL (Fin 2) ℝ)) τ‖) :
    ∃ f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) c, ∀ τ : UpperHalfPlane, f τ * Ψ τ = Φ τ := by sorry
