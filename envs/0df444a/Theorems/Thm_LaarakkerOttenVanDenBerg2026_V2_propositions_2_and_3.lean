-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_V2_propositions_2_and_3
-- name    : LaarakkerOttenVanDenBerg2026.V2.propositions_2_and_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T07:43:04.669862+00:00
-- url     : https://prove2.me/theorems/f1c966b1-2d31-4dc8-85b6-7b170b3cd92a
-- title:
--   Propositions 2–3: Quantifier interchange and constant families
-- statement:
--   For every contextual core theory, small dependent products commute up to internal half-adjoint equivalence with universal size quantification, and small dependent sums commute with existential size quantification. In every parametric theory, existential and universal quantification of a size-independent small type each give an internally equivalent type. Empty small domains and arbitrary contextual small families are included.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 2, Propositions 2 and 3, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryRevision2

namespace LaarakkerOttenVanDenBerg2026.V2

universe u v w t
open Theory

/-- The two definable interchange equivalences need only the core theory;
the fixed-small-type equivalences hold in the parametric theory. -/
theorem propositions_2_and_3 {C : CwF.{u,v,w,t}} :
    (∀ T : CoreTheory C, T.DefinableQuantifierEquivalences) ∧
    (∀ T : ParametricTheory C, T.toCoreTheory.ConstantQuantifierEquivalences) := by
  sorry

end LaarakkerOttenVanDenBerg2026.V2
