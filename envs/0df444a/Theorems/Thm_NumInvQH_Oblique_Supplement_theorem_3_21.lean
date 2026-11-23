-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_theorem_3_21
-- name    : NumInvQH.Oblique.Supplement.theorem_3_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:44:06.093941+00:00
-- url     : https://prove2.me/theorems/dd40d6f8-f075-41d1-9373-033288aada78
-- title:
--   Theorem 3.21 (corrected: filtration/restart conventions)
-- statement:
--   Let $S=(1,Y)$ be a locally square-integrable semimartingale market with at least two assets, on a probability space with trivial initial sigma algebra and the usual filtration conditions. The entire quadratic-hedging assertion of Theorem 4.1 holds: under a strictly positive deflator there exists the unique bounded opportunity semimartingale characterized by (1)(a)–(e); for every predictable adjustment and pure-hedge selection there is an admissible optimal strategy with the tracking-value, feedback and residual-error formulas (4.5)–(4.11); and the converse drops the deflator assumption. In particular,
--   $$\varphi=\xi+a(V_--\varphi S_-),\qquad E[(\varphi_TS_T-H)^2]=L_0(v-V_0)^2+\varepsilon_0^2(H).$$
--   The nice-numeraire premise is absent because the designated asset is identically one. All characterizing clauses, the some/any equivalence and all choices of $v\in\mathbb R$, $H\in L^2(P)$ are retained. The restart holding is explicitly fully invested at its initial time. This is the source constant-numeraire companion, not just one consequence of Theorem 4.1.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
--   - correction: a filtered probability space without explicitly requiring the usual conditions → the usual conditions are explicit in Usual P ℱ; reason: the source uses càdlàg density and conditional-value versions; bare filtrations can fail right continuity and Theorems 3.21/4.1 then fail (the bounded two-period example in DISPROOF.md has L(1/2)=19/20 and right limit 1 or 9/10). This excludes non-right-continuous or uncompleted filtrations, and matches the usual stochastic-calculus setting invoked through [22]
--   - encoding: weighted drift and covariance formulas involving c and F → the exactly equivalent compensator-rate identities (D.8)–(D.11); reason: the source proves these identities on pp. 35–36; normalization by 1+ΔB retains (4.1), (4.2), (4.8) and (4.10) for arbitrary clocks and jumps
--   - correction: -a 1_(τ,T] E(-(a1_(τ,T]) • S)_- belongs to the class with wealth one at τ → the displayed holdings are retained for t>τ and the holding at τ is Sτ/(Sτ·Sτ); reason: Definition 3.3 includes the initial value at τ and Definition 3.14 fixes it to one, whereas the printed indicator gives zero; the nice wealth ensures Sτ≠0. The constant market S=(1,0) is a counterexample to the printed endpoint; see DISPROOF.md
--   - encoding: the common clock for the payoff-dependent characteristics and the nonnegative residual integral in (4.9) → the supplied common clock retains the original adjustment selection, and both the path integral and conditional expectation of the residual use extended nonnegative integration; reason: this keeps the feedback and error conclusions available for the originally chosen adjustment process and prevents nonintegrable path integrals from silently becoming zero
--   - encoding: the stochastic logarithms in the well-defined weighted rates of Lemma D.1 and the as-above data of Lemma D.2 → LogDefined requires existence of the actual defining stochastic integral; WeightedRates carries that guard and Lemma D.2 names it explicitly; reason: positive left limits alone do not justify a logarithm after a zero-and-recovery path; this retains the source definedness requirement instead of accepting a zero fallback, and excludes no instance in which the source expressions are defined
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 12, Theorem 3.21

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Hedging

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

/-- Theorem 4.1 in a market whose first asset is one; no nice-numeraire premise. -/
theorem theorem_3_21 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (husual : Usual P ℱ)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ} (hd : 2 ≤ d) (S : Process Ω (Fin d → ℝ))
    (hS : LocallySquareIntegrable P ℱ T S) (first : Fin d)
    (hfirst : Same P T (fun t ω => S t ω first) (fun _ _ => 1)) :
    QuadraticHedgingTheorem P ℱ T S := by sorry

end NumInvQH.Oblique.Supplement
