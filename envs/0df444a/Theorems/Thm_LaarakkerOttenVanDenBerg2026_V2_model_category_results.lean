-- Prove2me | Theorems.Thm_LaarakkerOttenVanDenBerg2026_V2_model_category_results
-- name    : LaarakkerOttenVanDenBerg2026.V2.model_category_results
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-17T07:44:22.117463+00:00
-- url     : https://prove2.me/theorems/02611dd5-3b5f-45a6-bfe2-bed624d1e492
-- title:
--   Lemmas 15 and 17, Proposition 31: PERs, modest reflection and products
-- statement:
--   At every ambient universe level, the category of PERs over natural numbers is equivalent to the category of K1 modest assemblies; the specified modest-reflection functor is left adjoint to the inclusion into assemblies; and a dependent assembly product is modest whenever each codomain fiber is modest, even if its domain assembly is large. The equivalence and adjunction are actual categorical structures.
-- source:
--   Laarakker, Otten and van den Berg, Constructing (Co)inductive Types via Large Sizes, arXiv:2602.18921v2, Section 4, Lemmas 15 and 17; Appendix C, Proposition 31, https://arxiv.org/abs/2602.18921v2

import Definitions.Def_LaarakkerOttenVanDenBerg2026_ModelRevision2

namespace LaarakkerOttenVanDenBerg2026.V2

open CategoryTheory
universe u

/-- PER–modest equivalence, modest reflection, and modest dependent products. -/
theorem model_category_results :
    Nonempty (PER ≌ Modest.{u}) ∧
    Nonempty (modestReflection.{u} ⊣ modestInclusion.{u}) ∧
    ∀ (A : Assembly.{u}) (B : A.Carrier → Assembly.{u}),
      (∀ a, Assembly.IsModest (B a)) → Assembly.IsModest (Assembly.pi A B) := by
  sorry

end LaarakkerOttenVanDenBerg2026.V2
