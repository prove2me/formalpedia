-- Prove2me | Theorems.Thm_NonlinSSD_DualFunctional_theorem_4_dual_functional_formula
-- name    : NonlinSSD.DualFunctional.theorem_4_dual_functional_formula
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T03:23:13.302287+00:00
-- url     : https://prove2.me/theorems/8a065062-6637-42bb-a52d-b5f1309783d1
-- title:
--   Theorem 4 — D_i(v, ζ) = −E[v^*(ζ) + v(Y_i)] for v ∈ 𝒰₁([a,b]), ζ ∈ 𝓛∞
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space, $Y$ an integrable random variable (the reference outcome $Y_i$), $a\le b$, $v\in\mathcal U_1([a,b])$ and $\zeta\in\mathcal L_\infty$. Let $D$ be the dual functional (34),
--   $$D(v,\zeta)=\sup_{X\in\mathcal L_1}\mathbb E\big[v(X)-v(Y)-\zeta X\big],$$
--   and $v^*(\xi)=\inf_t[\xi t-v(t)]$ the concave conjugate. Theorem 4 of the paper asserts
--   $$D(v,\zeta)=-\mathbb E\big[v^*(\zeta)+v(Y)\big].$$
--   Precisely:
--
--   1. If $0\le\zeta\le v'_-(a)$ almost surely, then $v^*(\zeta)$ is almost surely finite, its real part is integrable, and
--   $$D(v,\zeta)=-\mathbb E\big[v^*(\zeta)+v(Y)\big]\in\mathbb R .$$
--   2. Otherwise, $D(v,\zeta)=+\infty$.
--
--   The theorem computes the contribution of one dominance constraint to the Lagrangian dual of the problem in closed form: the supremum over random outcomes $X$ decomposes into independent scalar maximizations, one for each $\omega$, whose value is a concave conjugate. It is the basis of the decomposition methods of §4 of the paper.
--
--   **Formalization Note** The right-hand side is the expectation of an extended-real random variable. Outside the domain $0\le\zeta\le v'_-(a)$ a.s., $v^*(\zeta)=-\infty$ on a set of positive probability and the paper reads both sides as $+\infty$; the two cases above make this convention explicit and avoid extended-real subtraction. In case 1 the expectation is the Bochner integral of $\omega\mapsto (v^*(\zeta(\omega)))_{\mathbb R}+v(Y(\omega))$, where the real part is taken of an almost surely finite value. $D$ is `EReal`-valued; the supremum ranges over integrable $X$. The index $i$ of the paper plays no role and is dropped.
-- source:
--   Dentcheva, Ruszczyński, Optimality and duality theory for stochastic optimization problems with nonlinear dominance constraints, author manuscript (rev. April 2003; Math. Program. 2004, DOI 10.1007/s10107-003-0453-z), p. 12, Theorem 4 (proof p. 13)

import Mathlib
import Definitions.Def_NonlinSSD_DualFunctional_Basic

open MeasureTheory

namespace NonlinSSD.DualFunctional

theorem theorem_4_dual_functional_formula {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hY : Integrable Y P) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → ℝ) (hv : v ∈ NonlinSSD.Optimality.U1 a b) (ζ : Ω → ℝ) (hζ : MemLp ζ ⊤ P) :
    ((∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a) →
      (∀ᵐ ω ∂P, concaveConj v (ζ ω) ≠ ⊥) ∧
      Integrable (fun ω => (concaveConj v (ζ ω)).toReal) P ∧
      dualD P Y v ζ = ((-∫ ω, ((concaveConj v (ζ ω)).toReal + v (Y ω)) ∂P : ℝ) : EReal)) ∧
    (¬ (∀ᵐ ω ∂P, 0 ≤ ζ ω ∧ ζ ω ≤ leftDeriv v a) → dualD P Y v ζ = ⊤) := by sorry

end NonlinSSD.DualFunctional
