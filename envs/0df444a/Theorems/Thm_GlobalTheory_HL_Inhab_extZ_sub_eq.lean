-- Prove2me | Theorems.Thm_GlobalTheory_HL_Inhab_extZ_sub_eq
-- name    : GlobalTheory.HL.Inhab.extZ_sub_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:31.832812+00:00
-- url     : https://prove2.me/theorems/b376b435-3e5e-5f96-8ba3-343f7ee07d44
-- title:
--   Inhab: ext Z sub eq
-- statement:
--   The Inhab construction uses the ext Z sub eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L361-L367
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HermitianFourInverseMul.lean#L361-L367

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIntegralIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HermitianFourInverseMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.Inhab
open GlobalTheory.HL.Model
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {s m N : ℕ} (e : Fin s ⊕ Fin m ≃ Fin N)

theorem GlobalTheory.HL.Inhab.extZ_sub_eq (x y z : Fin s → E) (c : E) (h : x - y = c • z) :
    extZ e x - extZ e y = c • extZ e z := by sorry
