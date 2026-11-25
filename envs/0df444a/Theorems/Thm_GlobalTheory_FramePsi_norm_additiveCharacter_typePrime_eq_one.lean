-- Prove2me | Theorems.Thm_GlobalTheory_FramePsi_norm_additiveCharacter_typePrime_eq_one
-- name    : GlobalTheory.FramePsi.norm_additiveCharacter_typePrime_eq_one
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:28:25.394547+00:00
-- url     : https://prove2.me/theorems/cbc3cd06-9906-5dc1-b06d-de2f60996bd1
-- title:
--   Frame Psi: norm additive Character type Prime eq one
-- statement:
--   The Frame Psi construction uses the norm additive Character type Prime eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormAdditiveCharacterTypePrimeEqOne.lean#L102-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/NormAdditiveCharacterTypePrimeEqOne.lean#L102-L109

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NormAdditiveCharacterTypePrimeEqOne
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
open GlobalTheory GlobalTheory.FramePsi
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem GlobalTheory.FramePsi.norm_additiveCharacter_typePrime_eq_one [IsNonarchimedeanLocalField F] (L : LocE F E) (y : E) : ‖L.psi0 y‖ = 1 := by sorry
