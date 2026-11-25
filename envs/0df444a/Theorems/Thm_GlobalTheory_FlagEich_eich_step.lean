-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_eich_step
-- name    : GlobalTheory.FlagEich.eich_step
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T08:41:12.841188+00:00
-- url     : https://prove2.me/theorems/52b3bd48-b1c7-46aa-8359-2de558b1f7ca
-- title:
--   Flag Eich: eich step
-- statement:
--   The Flag Eich construction uses the eich step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L124-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L124-L148

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_EichlerIsometry
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MemFlagUnipotentIffOrderedEichlerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.FlagEich
open GlobalTheory.HL.Eichler
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem GlobalTheory.FlagEich.eich_step {g : Fin (r + 1) → S.V}
    (H0 : ∀ a b : Fin r, hf L S.Hm (g a.castSucc) (g b.castSucc) = 0) (i : Fin r) (w : S.V) (t : E)
    (hw : ∀ j : Fin r, j ≤ i → hf L S.Hm w (g j.castSucc) = 0) :
    (∀ j : Fin r, ∀ v ∈ S.spanTo g ((j : ℕ) + 1),
      eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g j) ∧
    (∀ v ∈ perp L S.Hm (S.spanTo g r), eich L S.Hm (g i.castSucc) w t v - v ∈ S.spanTo g r) := by sorry
