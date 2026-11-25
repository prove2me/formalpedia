-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_expand
-- name    : GlobalTheory.FlagEich.expand
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:15.463908+00:00
-- url     : https://prove2.me/theorems/ab4d0cc3-69bb-55d9-8084-b176c16caec9
-- title:
--   Flag Eich: expand
-- statement:
--   The Flag Eich construction uses the expand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L86-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L86-L98

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

theorem GlobalTheory.FlagEich.expand {g : Fin (r + 1) → S.V} {gs : Fin r → S.V}
    (H1 : ∀ (a : Fin (r + 1)) (j : Fin r), hf L S.Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (x : S.V) (hx : x ∈ S.spanTo g r) : x = ∑ a : Fin r, hf L S.Hm x (gs a) • g a.castSucc := by sorry
