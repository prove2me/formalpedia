-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_lemma_3_11
-- name    : NumInvQH.Oblique.Supplement.lemma_3_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:41:42.267774+00:00
-- url     : https://prove2.me/theorems/a52139c5-bc63-47ec-8737-0aad610f90cd
-- title:
--   Lemma 3.11 — For every admissible ϑ ∈ Θ̄(S,P) and every deflator Z ∈ M2(S,P), Z(ϑS) is a P-martingale.
-- statement:
--   For any semimartingale market $S$, every admissible strategy $\theta\in\overline\Theta(S,P)$ and every deflator $Z\in M_2(S,P)$ satisfy
--   $$Z(\theta S)\text{ is a }P\text{-martingale on }[0,T].$$
--   Here admissibility is the closure in Definition 3.9 and the deflator tests tame zero-initial wealth and a positive self-financing wealth as in Definition 3.10. This transfers the deflator property to the full admissible class; no local square-integrability assumption on $S$ is added.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 8, Lemma 3.11

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Market

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem lemma_3_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ} (hd : 2 ≤ d)
    (S θ : Process Ω (Fin d → ℝ)) (Z : Process Ω ℝ) (hS : Semi P ℱ T S)
    (hθ : Admissible P ℱ T S θ) (hZ : Deflator P ℱ T S Z) :
    Martingale (stop T (fun t ω => Z t ω * wealth θ S t ω)) ℱ P := by sorry

end NumInvQH.Oblique.Supplement
