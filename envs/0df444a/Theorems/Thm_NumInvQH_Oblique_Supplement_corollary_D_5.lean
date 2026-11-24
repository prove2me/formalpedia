-- Prove2me | Theorems.Thm_NumInvQH_Oblique_Supplement_corollary_D_5
-- name    : NumInvQH.Oblique.Supplement.corollary_D_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T21:50:50.51798+00:00
-- url     : https://prove2.me/theorems/44d239c1-438e-419b-a5e9-a37eeb0cb087
-- title:
--   Corollary D.5 (corrected: source conventions) — restarted exponential identity
-- statement:
--   In the Appendix D setting let $\tau\le T$ be a stopping time, with $1_{(\tau,T]}\widehat\alpha\in L(\widehat S)$ and $\widehat\alpha\widehat S_-=1$ on $(\tau,T]$. Then the undiscounted restarted integrand is integrable and, on $[\tau,T]$,
--   $$\mathcal E((1_{(\tau,T]}\widehat\alpha/X_-)\mathbin\bullet S)
--   =\mathcal E((1_{(\tau,T]}\widehat\alpha)\mathbin\bullet\widehat S)X/X_\tau.$$
--   The identity includes the value one at the restart time. This is the restarted version of (D.17).
--
--   The initial sigma field is $P$-trivial, as in the standing setting on p. 2.
--
--   Differences from the source:
--   - encoding: finite-horizon vector processes and stochastic equality → Fin-indexed coordinates, stopped extensions and indistinguishability on [0,T]; reason: this preserves the full finite-horizon domain, including null modifications and arbitrary finite dimension d ≥ 2
--   - encoding: the general predictable vector integral of [22, III.6.17] → elementary-sum construction followed by bounded predictable extension and Emery convergence of joint truncations; reason: this constructs general vector integration and retains cancellation; it does not impose coordinatewise integrability, absolute continuity of characteristics, or calculus axioms
--   - encoding: stochastic integrals, brackets, logarithms, exponentials and conditional processes → chosen genuine versions from explicit defining relations; reason: these quantities are unique up to indistinguishability on the stated domain; their outside-domain zero defaults are not hypotheses or replacement values for source objects
--   - correction: the restarted identity with X/Xτ has no explicitly written time domain → the identity is asserted on [[τ,T]] including τ; reason: before τ the left exponential is one but X_t/Xτ need not be one; with deterministic X_t=1+t and τ=1/2 the printed global identity fails. The proof on p.37 splits at τ, supporting the restarted domain
-- source:
--   Černý, Czichowsky & Kallsen, Numeraire-invariant quadratic hedging and mean–variance portfolio allocation, arXiv:2110.09416v4, pp. 37, Corollary D.5

import Mathlib
import Definitions.Def_NumInvQH_Oblique_Supplement_Numeraire

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace NumInvQH.Oblique.Supplement

/-- The restarted identity is an identity on [[τ,T]], as its proof's restart convention requires. -/
theorem corollary_D_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (h0 : ∀ A, MeasurableSet[ℱ 0] A → P A = 0 ∨ P A = 1)
    (T : ℝ≥0) {d : ℕ}
    (S αh : Process Ω (Fin d → ℝ)) (first : Fin d) (hD : AppendixD P ℱ T S first)
    (τ : BoundedStop ℱ T)
    (hα : ∃ I, HasIntegral (changedMeasure P T (fun t ω => S t ω first)) ℱ T
      (after τ.time αh) (discounted S (fun t ω => S t ω first)) I)
    (hunit : ∀ᵐ ω ∂P, ∀ t, τ.time ω < t → t ≤ T →
      αh t ω ⬝ᵥ left (discounted S (fun t ω => S t ω first)) t ω = 1) :
    let X := fun t ω => S t ω first
    let Q := changedMeasure P T X
    let α := after τ.time (fun t ω => (left X t ω)⁻¹ • αh t ω)
    (∃ I, HasIntegral P ℱ T α S I) ∧
    ∀ᵐ ω ∂P, ∀ t, τ.time ω ≤ t → t ≤ T →
      exponential P ℱ T (integral P ℱ T α S) t ω =
        exponential Q ℱ T (integral Q ℱ T (after τ.time αh) (discounted S X)) t ω *
          X t ω / X (τ.time ω) ω := by sorry

end NumInvQH.Oblique.Supplement
