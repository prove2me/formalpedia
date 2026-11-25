-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_mem_Nof
-- name    : GlobalTheory.FlagEich.mem_Nof
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T08:39:19.983746+00:00
-- url     : https://prove2.me/theorems/8ae630e7-e406-4e1e-bcb3-89370aac334f
-- title:
--   Flag Eich: mem Nof
-- statement:
--   The Flag Eich construction uses the mem Nof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L105-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L105-L108

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

theorem GlobalTheory.FlagEich.mem_Nof {g : Fin (r + 1) → S.V} {n : S.GLV} : n ∈ S.Nof g ↔ n ∈ isomG L S.Hm ∧
    (∀ j : Fin r, n ∈ unipOn (S.spanTo g ((j : ℕ) + 1)) (S.spanTo g j)) ∧
    n ∈ unipOn (perp L S.Hm (S.spanTo g r)) (S.spanTo g r) := by sorry
