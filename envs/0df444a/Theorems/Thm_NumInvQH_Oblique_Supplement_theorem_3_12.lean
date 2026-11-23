-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_theorem_3_12
-- name    : NumInvQH.Oblique.Supplement.theorem_3_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:42:39.244238+00:00
-- url     : https://prove2.me/theorems/6847f106-f3df-4c74-aa04-2d3473739795
-- title:
--   Theorem 3.12 — A strictly positive deflator in M2(S,P) and Θ̄v(S,P) ≠ ∅ give an optimizer of the quadratic hedging problem (1.2) over Θ̄v(S,P); its valu…
-- statement:
--   Let $S$ be any semimartingale market on a filtered probability space with trivial initial sigma algebra, let $v\in\mathbb R$ and let $H\in L^2(P)$. Suppose there is a strictly positive deflator and the admissible class with initial wealth $v$ is nonempty. Then
--   $$\operatorname*{argmin}_{\theta\in\overline\Theta_v(S,P)}E[(\theta_TS_T-H)^2]\ne\varnothing.$$
--   Any two optimizers have indistinguishable wealth processes on $[0,T]$. The statement neither asserts uniqueness of the holdings nor assumes local square integrability of $S$. It is the existence and wealth-uniqueness companion to the explicit finite-dimensional formulas.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 8, Theorem 3.12

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Market

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem theorem_3_12 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ} (hd : 2 ≤ d) (S : Process Ω (Fin d → ℝ))
    (hS : Semi P ℱ T S) (v : ℝ) (H : Ω → ℝ) (hH : MemLp H 2 P)
    (hZ : ∃ Z, Deflator P ℱ T S Z ∧ ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < Z t ω)
    (hne : ∃ θ, Admissible P ℱ T S θ ∧ ∀ᵐ ω ∂P, wealth θ S 0 ω = v) :
    (∃ θ, Optimal P ℱ T S θ v H) ∧
    ∀ θ η, Optimal P ℱ T S θ v H → Optimal P ℱ T S η v H →
      Same P T (wealth θ S) (wealth η S) := by sorry

end NumInvQH.Oblique.Supplement
