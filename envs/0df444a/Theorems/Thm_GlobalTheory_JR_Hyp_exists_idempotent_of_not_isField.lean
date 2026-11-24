-- Prove2me | Theorems.Thm_GlobalTheory_JR_Hyp_exists_idempotent_of_not_isField
-- name    : GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:33:21.915584+00:00
-- url     : https://prove2.me/theorems/b532f7d3-8c51-4f5e-9802-984cece69788
-- title:
--   Hyp: exists idempotent of not is Field
-- statement:
--   The Hyp construction uses the exists idempotent of not is Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIdempotentStarEqOneSubOfNotIsField.lean#L8-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIdempotentStarEqOneSubOfNotIsField.lean#L8-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WHyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIdempotentStarEqOneSubOfNotIsField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.Hyp

theorem GlobalTheory.JR.Hyp.exists_idempotent_of_not_isField : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → ¬ IsField A.L → ∃ e : A.L, e * e = e ∧ star e = 1 - e := by sorry
