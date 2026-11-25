-- Prove2me | Theorems.Thm_GlobalTheory_HL_PairingClass_Tied_inv
-- name    : GlobalTheory.HL.PairingClass.Tied.inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T06:22:52.765663+00:00
-- url     : https://prove2.me/theorems/2cae1910-0a94-5434-aea6-5bfc6f59e074
-- title:
--   Tied: inv
-- statement:
--   The Tied construction uses the inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverRelationUniqueness.lean#L75-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TermOverRelationUniqueness.lean#L75-L85

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_IsTermOver
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ComplementReferenceCompactSubgroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_GgNone
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToLePerp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_FramesCommonStabiliserEqPairingMatrixStabiliser
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_NotField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SpanToZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TermOverRelationUniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.HL GlobalTheory.HL.PairingClass
variable {E : Type} [CommRing E] {n : ℕ}

theorem GlobalTheory.HL.PairingClass.Tied.inv {O : Subring E} {θ : E} {A A' : Matrix (Fin n) (Fin n) E} (hA : Tied O θ A A') :
    ∃ B B', Tied O θ B B' ∧ A * B = 1 ∧ B * A = 1 ∧ A' * B' = 1 ∧ B' * A' = 1 := by sorry
