-- Prove2me | Theorems.Thm_GlobalTheory_corr_of_corr_pullGen
-- name    : GlobalTheory.corr_of_corr_pullGen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:29.933611+00:00
-- url     : https://prove2.me/theorems/a089b53d-edf7-4796-af01-722b04240c07
-- title:
--   Global Theory: corr of corr pull Gen
-- statement:
--   The Global Theory construction uses the corr of corr pull Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CorrOfGenericOfIsSeparated.lean#L12-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CorrOfGenericOfIsSeparated.lean#L12-L30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsSchemeTheoreticallyDominantSpecOfInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CorrOfGenericOfIsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory
universe u

theorem GlobalTheory.corr_of_corr_pullGen {X Y Z : Scheme.{u}} (L : LB X) {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → (Y ⟶ X)) (ε : I → ℤ) (φ' : I' → (Y ⟶ X)) (ε' : I' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (h : Z ⟶ Y)
    (hinj : ∀ U, Function.Injective (h.app U).hom) (hc : ∀ a b : Y ⟶ X, h ≫ a = h ≫ b → a = b)
    (H : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t h) (LB.pullGen L _ _ t' h)) :
    LB.Gen.Corr L _ _ _ _ t t' := by sorry
