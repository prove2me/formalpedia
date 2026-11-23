-- Prove2me | Theorems.Thm_NoHair_not_hawking_analytic_nondegenerate_vacuum
-- name    : NoHair.not_hawking_analytic_nondegenerate_vacuum
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:05:45.907107+00:00
-- url     : https://prove2.me/theorems/577a50a5-c25a-4d12-8350-33552d73af48
-- title:
--   The analytic vacuum uniqueness claim fails for the enlarged Kerr end
-- statement:
--   The analytic vacuum uniqueness implication fails with the reference-end predicate in the linked milestone. Writing $D_E=I^+(E)\cap I^-(E)$ for the domain determined by the chosen end, the negation has the form
--   $$
--   \neg\,\forall (M,g,F,T,\phi,E),\quad
--   \bigl[\text{stationary analytic vacuum black hole with nondegenerate horizon}\bigr]
--   \;\Longrightarrow\;
--   \exists\,m>0,\ a^2\le m^2,\quad (D_E,g)\cong D_{\mathrm{Kerr}}(m,a).
--   $$
--   Here the electromagnetic field is zero and the formal isometry also matches that field. A counterexample occurs on ordinary four-dimensional ingoing Kerr spacetime with mass $5/2$ and spin $2$. The permitted end $r>1$ includes the region between the horizons. The standard timelike reference region in the classical uniqueness theorem is specified in Chruściel and Costa, §2.2, equation (2.9).
-- source:
--   Counterexample to the exact Prove2Me statement NoHair.hawking_analytic_nondegenerate_vacuum, https://prove2.me/theorems/d3c7be7a-309a-40fd-b177-28ba5a1b316c . Explicit Kerr construction, https://prove2.me/theorems/c4698ceb-01fb-4c66-997c-a1115474b338 . For the classical choice of reference region compare Chruściel and Costa (2008), Section 2.2, equation (2.9), https://arxiv.org/abs/0806.0016 .

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.not_hawking_analytic_nondegenerate_vacuum : ¬ (∀ {M : Type} [TopologicalSpace M] [ChartedSpace E4 M]
    [IsManifold 𝓘(ℝ,E4) ∞ M] [IsManifold 𝓘(ℝ,E4) ω M]
    (g F : BilinField M) (T : VecField M) (φ : ℝ → M → M) (E : AsymptoticallyFlatEnd g F φ),
    IsStationaryBlackHole g F T φ E → (∀ x, F x = 0) → IsAnalyticBilinField g →
      IsNondegenerateHorizon g F (futureEventHorizon g T E.region)
        (domainOfOuterCommunications g T E.region) →
      ∃ m a : ℝ, IsKerrNewmanBlackHoleParams m a 0 ∧
        IsKerrNewmanDOC g F (domainOfOuterCommunications g T E.region) m a 0) := by
  sorry
