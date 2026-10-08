-- Prove2me | Theorems.Thm_InfoGen_Gibbs_klDiv_dirac_eq
-- name    : InfoGen.Gibbs.klDiv_dirac_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:27:40.115534+00:00
-- url     : https://prove2.me/theorems/6f96f4fe-d1fc-464f-a861-f699e2ea433e
-- title:
--   Appendix D, p. 13 — KL divergence of a point mass
-- statement:
--   Let $Q$ be a probability distribution on a countable hypothesis space and let $w$ be a hypothesis to which $Q$ assigns positive mass. Then
--   $$D(\delta_w\Vert Q)=-\log Q(\{w\}).$$
--   The identity converts the comparison with a fixed hypothesis into the logarithmic prior-mass term in Corollary 2.
--
--   **Formalization Note** The paper states the identity for its minimizer $w_o$; the same formula holds for any $w$ with positive prior mass. Positivity excludes the infinite divergence case, since Lean's real logarithm at zero would otherwise give a junk value.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, App. D, final sentence after (D.15), p. 13

import Mathlib
import Definitions.Def_InfoGen_Gibbs_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace InfoGen.Gibbs

/-- The last sentence of Appendix D, PDF p. 13. -/
theorem klDiv_dirac_eq {W : Type*} [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (Q : Measure W) [IsProbabilityMeasure Q] (w : W)
    (hQ : Q {w} ≠ 0) :
    klDiv (Measure.dirac w) Q =
      ENNReal.ofReal (-Real.log (Q {w}).toReal) := by sorry

end InfoGen.Gibbs
