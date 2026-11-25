-- Prove2me | Theorems.Thm_GlobalTheory_HermOrthBasis_isCompl_perp
-- name    : GlobalTheory.HermOrthBasis.isCompl_perp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T06:08:54.149128+00:00
-- url     : https://prove2.me/theorems/a80c45c9-259a-4aa5-96da-b2170dc4ecb2
-- title:
--   Herm Orth Basis: is Compl perp
-- statement:
--   The Herm Orth Basis construction uses the is Compl perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/LeOfPerpEqBot.lean#L68-L78

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_HermLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LeOfPerpEqBot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HermOrthBasis
open Matrix
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable (L : LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)

theorem GlobalTheory.HermOrthBasis.isCompl_perp {m : ℕ} (x : Fin m → Fin n → E) (hx : IsUnit (gramT L Hm x).det) :
    IsCompl (Submodule.span E (Set.range x)) (perp L Hm (Submodule.span E (Set.range x))) := by sorry
