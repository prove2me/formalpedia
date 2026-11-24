-- Prove2me | Theorems.Thm_GlobalTheory_DI_delta_sub
-- name    : GlobalTheory.DI.delta_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:49:51.648721+00:00
-- url     : https://prove2.me/theorems/530bcc32-9efd-4444-a972-823684188829
-- title:
--   DI: delta sub
-- statement:
--   The DI construction uses the delta sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CechAndTotalDifferentialAdditiveSquareZero.lean#L13-L15

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechAndTotalDifferentialAdditiveSquareZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
variable {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]

theorem GlobalTheory.DI.delta_sub (c c' : Finset ι → E) : delta (c - c') = delta c - delta c' := by sorry
