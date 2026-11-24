-- Prove2me | Theorems.Thm_GlobalTheory_SplitLift_cT_adj_mul
-- name    : GlobalTheory.SplitLift.cT_adj_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:21:29.665881+00:00
-- url     : https://prove2.me/theorems/0c180d2d-9f05-484f-a1c1-08345f5a4dba
-- title:
--   Split Lift: c T adj mul
-- statement:
--   The Split Lift construction uses the c T adj mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L185-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsUnitaryStabilizerLiftOfSplitIdempotent.lean#L185-L192

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

theorem GlobalTheory.SplitLift.cT_adj_mul (s : A →+* A) (hs : ∀ a, s (s a) = a) {J : Matrix (Fin n) (Fin n) A}
    (hH : IsHerm s J) (hJ : IsUnit J.det)
    (X : Matrix (Fin n) (Fin n) A) : cT s (adj s J X) * J = J * X := by sorry
