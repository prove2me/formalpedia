-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_lemma_D_4
-- name    : NumInvQH.Oblique.Supplement.lemma_D_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:49:45.731286+00:00
-- url     : https://prove2.me/theorems/049a2d58-6e9f-44a7-a3cb-b0f77a94741f
-- title:
--   Lemma D.4 — For α ∈ L(S) with αS− = 1, ϑ = αE(α•S)− is self-financing with ϑS = E(α•S); with α̂ = αX−, α̂ ∈ L(Ŝ) and E(α•S) = E(α̂•Ŝ)X/X0.
-- statement:
--   In the Appendix D setting, suppose $\alpha\in L(S)$ and $\alpha S_-=1$. Put $E=\mathcal E(\alpha\mathbin\bullet S)$, $\theta=\alpha E_-$ and $\widehat\alpha=\alpha X_-$. Then $\theta$ is self-financing, its wealth is $E$, and $\widehat\alpha\in L(\widehat S)$. Moreover,
--   $$\mathcal E(\alpha\mathbin\bullet S)=\mathcal E(\widehat\alpha\mathbin\bullet\widehat S)X/X_0.$$
--   All equalities are up to indistinguishability. This transfers fully invested exponential wealth without imposing boundedness or coordinatewise integrability on $\alpha$.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 37, Lemma D.4

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem lemma_D_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ}
    (S α : Process Ω (Fin d → ℝ)) (first : Fin d) (hD : AppendixD P ℱ T S first)
    (hα : ∃ I, HasIntegral P ℱ T α S I)
    (hunit : Same P T (fun t ω => α t ω ⬝ᵥ left S t ω) (fun _ _ => 1)) :
    let X := fun t ω => S t ω first
    let Sh := discounted S X
    let Q := changedMeasure P T X
    let E := exponential P ℱ T (integral P ℱ T α S)
    let θ := fun t ω => left E t ω • α t ω
    let αh := fun t ω => left X t ω • α t ω
    SelfFinancing P ℱ T S θ ∧ Same P T (wealth θ S) E ∧
    (∃ I, HasIntegral Q ℱ T αh Sh I) ∧
    Same P T E (fun t ω => exponential Q ℱ T (integral Q ℱ T αh Sh) t ω * X t ω / X 0 ω) := by sorry

end NumInvQH.Oblique.Supplement
