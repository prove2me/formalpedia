-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_adj_smul
-- name    : GlobalTheory.SplitLift.adj_smul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:56:26.038402+00:00
-- url     : https://prove2.me/theorems/d7face8a-e706-4688-97c3-391b8866495d
-- title:
--   Split Lift: adj smul
-- statement:
--   The Split Lift construction uses the adj smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L173-L175

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_GlobAut
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SemilocalFrames_ExistsReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsUnitaryStabilizerLiftOfSplitIdempotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
open GlobalTheory GlobalTheory.SplitLift
open Formalism.UG
variable {A : Type} [CommRing A] {n : ℕ}

theorem GlobalTheory.SplitLift.adj_smul (s : A →+* A) (J : Matrix (Fin n) (Fin n) A) (a : A)
    (X : Matrix (Fin n) (Fin n) A) : adj s J (a • X) = s a • adj s J X := by sorry
