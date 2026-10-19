-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_exists_polynomial_uniform_approx
-- name    : OAI.CrouzeixHilbert.exists_polynomial_uniform_approx
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:13.551984+00:00
-- url     : https://prove2.me/theorems/e98d05e5-2c9c-416f-bd24-5d6c8e39eee8
-- title:
--   Runge's theorem on compact convex sets: a function holomorphic near a compact convex set is a uniform limit of polynomials on it
-- statement:
--   Let $K \subseteq \mathbb C$ be compact (`IsCompact K`) and convex (`Convex ℝ K`, convex as a subset of the real vector space $\mathbb C$), and let $U \subseteq \mathbb C$ be an open set (`IsOpen U`) with $K \subseteq U$. Let $f : \mathbb C \to \mathbb C$ be complex differentiable on $U$ (`DifferentiableOn ℂ f U`), and let $\varepsilon > 0$ be real. Then there is a polynomial $p$ with complex coefficients (`p : Polynomial ℂ`) such that
--   $$|p(z) - f(z)| < \varepsilon \qquad \text{for every } z \in K.$$
--   In Lean $p(z)$ is `p.eval z`. If $K$ is empty the conclusion holds for any $p$.
--
--   A compact convex set has connected complement, so this is the polynomial case of Runge's approximation theorem (C. Runge, 1885) for compact convex sets.
--
--   Lean: `OAI.CrouzeixHilbert.exists_polynomial_uniform_approx`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/PolynomialApproximation.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   C. Runge, Zur Theorie der eindeutigen analytischen Functionen, Acta Math. 6 (1885), 229–244 (the theorem, for compact sets with connected complement); proof and Lean code: OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/PolynomialApproximation.lean (declaration OAI.CrouzeixHilbert.exists_polynomial_uniform_approx)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Topology

open Set Filter Metric MeasureTheory

namespace CrouzeixHilbert

theorem exists_polynomial_uniform_approx {K U : Set ℂ}
    (hK : IsCompact K) (hc : Convex ℝ K) (hU : IsOpen U) (hKU : K ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖p.eval z - f z‖ < ε := by
  sorry

open scoped Matrix.Norms.L2Operator

universe u

end CrouzeixHilbert

end

end OAI
end
