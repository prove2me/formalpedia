-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_V2_lemma_1_unique_fix
-- name    : LaarakkerOttenVanDenBerg2026.V2.lemma_1_unique_fix
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T07:42:49.046568+00:00
-- url     : https://prove2.me/theorems/c3978ca1-ca83-41fa-83e1-009c927e6428
-- title:
--   Lemma 1: Internal contractibility of size-recursive fixed points
-- statement:
--   In every contextual core theory, for every context, large family over sizes and contextual recursive step, the full internal dependent sum of a candidate function and its pointwise unfolding witness is contractible. Identity witnesses are retained; no external proof-irrelevant subtype or assumed uniqueness principle replaces this assertion.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 2, Lemma 1, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_TheoryRevision2

namespace LaarakkerOttenVanDenBerg2026.V2

universe u v w t
open Theory

/-- The internal type of fixed points, including their unfolding witnesses,
is contractible. No proof irrelevance for these witnesses is assumed. -/
theorem lemma_1_unique_fix {C : CwF.{u,v,w,t}} (T : CoreTheory C)
    {Γ : C.Ctx} (A : C.Ty (C.ext Γ (T.size.type Γ)))
    (f : C.Tm Γ (T.products.pi (T.size.type Γ)
      (T.functions.arr (T.size.bounded T.products T.functions A) A))) :
    Nonempty (C.Tm Γ (contractible T.products T.sums T.identities
      (T.size.fixedPointSolutions T.products T.functions T.sums T.sizeSubstitution A f))) := by
  sorry

end LaarakkerOttenVanDenBerg2026.V2
