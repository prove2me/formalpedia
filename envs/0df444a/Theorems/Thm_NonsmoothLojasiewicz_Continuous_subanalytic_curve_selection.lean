-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_subanalytic_curve_selection
-- name    : NonsmoothLojasiewicz.Continuous.subanalytic_curve_selection
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-28T06:25:45.817849+00:00
-- url     : https://prove2.me/theorems/3a2c616e-88c2-4b34-a847-58ef0ea96492
-- title:
--   Curve selection lemma for subanalytic sets
-- statement:
--   Let $X$ be a finite-dimensional real normed space, $A \subseteq X$ a subanalytic set and $x_0 \in \overline{A}$. Then there are a real-analytic path germ $\gamma$ at $0$ and $\varepsilon > 0$ with
--
--   $$\gamma(0) = x_0, \qquad \gamma(u) \in A \quad \text{for all } u \in (0,\varepsilon).$$
--
--   Role: the parent's proof selects an analytic arc through a limit point of the set where the Łojasiewicz inequality would fail, and derives the exponent from the order of vanishing along that arc.
--
--   **Formalization Note**: the source takes $a$ in the boundary of $A$ and a path analytic on $(-1,1)$; here $x_0$ is any point of the closure (for $x_0 \in A$ the constant path works) and only the germ of $\gamma$ at $0$ is required analytic, after rescaling the parameter.
-- source:
--   J. Bolte, A. Daniilidis, A. Lewis, The Lojasiewicz inequality for nonsmooth subanalytic functions with applications to subgradient dynamical systems, SIAM J. Optim. 17 (2007) 1205-1223, https://people.orie.cornell.edu/aslewis/publications/07-lojasiewicz.pdf, Section 2, p. 1208, Curve selection lemma (citing Bierstone-Milman)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic

namespace NonsmoothLojasiewicz.Continuous

theorem subanalytic_curve_selection {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (A : Set X) (hA : IsSubanalytic A) (x₀ : X) (hx₀ : x₀ ∈ closure A) :
    ∃ γ : ℝ → X, AnalyticAt ℝ γ 0 ∧ γ 0 = x₀ ∧ ∃ ε > 0, ∀ u ∈ Set.Ioo (0 : ℝ) ε, γ u ∈ A := by sorry

end NonsmoothLojasiewicz.Continuous
