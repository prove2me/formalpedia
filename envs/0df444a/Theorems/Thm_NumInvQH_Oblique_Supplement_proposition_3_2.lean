-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_proposition_3_2
-- name    : NumInvQH.Oblique.Supplement.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:40:56.481809+00:00
-- url     : https://prove2.me/theorems/e9dd3a1e-c160-4ef7-8fdf-b90fb396ca9e
-- title:
--   Proposition 3.2 — Three equivalent forms of the self-financing condition
-- statement:
--   Let $S$ be any vector semimartingale with at least two assets and let $\theta$ be a trading strategy. The following are equivalent: self-financing; integrability together with $W_0+(\theta\mathbin\bullet S)_-=\theta S_-$; and, for every scalar semimartingale $Z$, integrability with respect to $SZ$ together with
--   $$(W_0)Z_0+\theta\mathbin\bullet(SZ)=(\theta S)Z.$$
--   Self-financing also implies $W_-=\theta S_-$. Every equality is on the whole finite horizon up to indistinguishability. This is the source numeraire-invariance characterization, without a local square-integrability assumption.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 6–7, Proposition 3.2

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Market

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem proposition_3_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ} (hd : 2 ≤ d)
    (S θ : Process Ω (Fin d → ℝ)) (hS : Semi P ℱ T S) :
    (SelfFinancing P ℱ T S θ ↔
      (∃ I, HasIntegral P ℱ T θ S I ∧
        Same P T (fun t ω => wealth θ S 0 ω + left I t ω)
          (fun t ω => θ t ω ⬝ᵥ left S t ω))) ∧
    (SelfFinancing P ℱ T S θ ↔
      ∀ Z : Process Ω ℝ, ScalarSemi P ℱ T Z →
        HasIntegral P ℱ T θ (fun t ω i => S t ω i * Z t ω)
          (fun t ω => wealth θ S t ω * Z t ω - wealth θ S 0 ω * Z 0 ω)) ∧
    (SelfFinancing P ℱ T S θ →
      Same P T (left (wealth θ S)) (fun t ω => θ t ω ⬝ᵥ left S t ω)) := by sorry

end NumInvQH.Oblique.Supplement
