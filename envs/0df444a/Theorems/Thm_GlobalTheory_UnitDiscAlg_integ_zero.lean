-- Prove2me | Theorems.Thm_GlobalTheory_UnitDiscAlg_integ_zero
-- name    : GlobalTheory.UnitDiscAlg.integ_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:26:38.310872+00:00
-- url     : https://prove2.me/theorems/801d11dc-b660-48b0-b662-0c5db6762abe
-- title:
--   Unit Disc Alg: integ zero
-- statement:
--   The Unit Disc Alg construction uses the integ zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommOfBezout.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CommOfBezout.lean#L38-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_CentralizerTensorForms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NotCompactOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorOfSeparableCharpolyField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CyclicVectorGeneratedAlgebraStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommOfBezout
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.UnitDiscAlg
variable {E : Type} [NontriviallyNormedField E] [IsUltrametricDist E] {n : ℕ}

theorem GlobalTheory.UnitDiscAlg.integ_zero : ∀ i j, ‖(0 : Matrix (Fin n) (Fin n) E) i j‖ ≤ 1 := by sorry
