-- Prove2me | Theorems.Thm_GlobalTheory_FlagEich_prod_update
-- name    : GlobalTheory.FlagEich.prod_update
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:20.903158+00:00
-- url     : https://prove2.me/theorems/651b9c2d-1872-4c3d-ba04-1ff7b769a2d0
-- title:
--   Flag Eich: prod update
-- statement:
--   The Flag Eich construction uses the prod update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L15-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MemFlagUnipotentIffOrderedEichlerProduct.lean#L15-L36

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

theorem GlobalTheory.FlagEich.prod_update {G : Type*} [Group G] : ∀ {r : ℕ} (f : Fin r → G) (M : Fin r) (x : G),
    (∀ i, i ≤ M → f i = 1) → (List.ofFn (Function.update f M x)).prod = x * (List.ofFn f).prod := by sorry
