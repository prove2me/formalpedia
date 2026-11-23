-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_lemma_D_2
-- name    : NumInvQH.Oblique.Supplement.lemma_D_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:47:52.435344+00:00
-- url     : https://prove2.me/theorems/dbd82898-fdac-4854-a2b0-73b94b946117
-- title:
--   Lemma D.2 (corrected: source conventions) — Girsanov equivalence and equal compensators
-- statement:
--   In the Appendix D market, let $\widehat L$ be a $\widehat P$-semimartingale with positive left limit and let $W$ be any semimartingale. With $\widetilde Z_t=E[X_T^2\mid\mathcal F_t]$, define
--   $$U=W+[W,\mathcal L(\widehat L)],\qquad V=W+[W,\mathcal L(\widehat L\widetilde Z)].$$
--   Then $U$ is special under $\widehat P$ if and only if $V$ is special under $P$. Whenever these equivalent conditions hold, their canonical predictable finite-variation parts agree up to indistinguishability. This is the complete Girsanov transfer, including the equality of compensators.
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
--   - correction: a filtered probability space without explicitly requiring the usual conditions → the usual conditions are explicit in Usual P ℱ; reason: the source uses càdlàg density and conditional-value versions; bare filtrations can fail right continuity and Theorems 3.21/4.1 then fail (the bounded two-period example in DISPROOF.md has L(1/2)=19/20 and right limit 1 or 9/10). This excludes non-right-continuous or uncompleted filtrations, and matches the usual stochastic-calculus setting invoked through [22]
--   - encoding: the stochastic logarithms in the well-defined weighted rates of Lemma D.1 and the as-above data of Lemma D.2 → LogDefined requires existence of the actual defining stochastic integral; WeightedRates carries that guard and Lemma D.2 names it explicitly; reason: positive left limits alone do not justify a logarithm after a zero-and-recovery path; this retains the source definedness requirement instead of accepting a zero fallback, and excludes no instance in which the source expressions are defined
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 36–37, Lemma D.2

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

theorem lemma_D_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (husual : Usual P ℱ)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ}
    (S : Process Ω (Fin d → ℝ)) (first : Fin d) (hD : AppendixD P ℱ T S first)
    (Lh W : Process Ω ℝ)
    (hL : ScalarSemi (changedMeasure P T (fun t ω => S t ω first)) ℱ T Lh)
    (hleft : ∀ᵐ ω ∂P, ∀ t ≤ T, 0 < left Lh t ω)
    (hlog : LogDefined (changedMeasure P T (fun t ω => S t ω first)) ℱ T Lh)
    (hW : ScalarSemi P ℱ T W) :
    let X := fun t ω => S t ω first
    let Q := changedMeasure P T X
    let Zt := densityNumerator P ℱ T X
    let U := fun t ω => W t ω + covariation Q ℱ T W (stochasticLog Q ℱ T Lh) t ω
    let V := fun t ω => W t ω + covariation P ℱ T W
      (stochasticLog P ℱ T (fun t ω => Lh t ω * Zt t ω)) t ω
    (Special Q ℱ T U ↔ Special P ℱ T V) ∧
    (Special Q ℱ T U → Same P T (compensator Q ℱ T U) (compensator P ℱ T V)) := by sorry

end NumInvQH.Oblique.Supplement
