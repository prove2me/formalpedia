-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Tower_fv_nsmul
-- name    : GlobalTheory.AdLat.Tower.fv_nsmul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:35:29.576001+00:00
-- url     : https://prove2.me/theorems/42314464-e1f7-4c6b-887f-a36db2526a55
-- title:
--   Tower: fv nsmul
-- statement:
--   The Tower construction uses the fv nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLinearApproxTower.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLinearApproxTower.lean#L26-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
import Theorems.Thm_GlobalTheory_AdLat_Translate_fv_nsmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Tower
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
omit [NumberField E]

theorem GlobalTheory.AdLat.Tower.fv_nsmul (N : ℕ) (x : Fin n → E) : fv F (N • x) = N • fv F x := by sorry
