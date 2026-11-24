-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Tower_nsmul_cancel
-- name    : GlobalTheory.AdLat.Tower.nsmul_cancel
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:58:29.61917+00:00
-- url     : https://prove2.me/theorems/3bab56b2-29bf-4da2-929e-84ca489d898e
-- title:
--   Tower: nsmul cancel
-- statement:
--   The Tower construction uses the nsmul cancel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLinearApproxTower.lean#L39-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLinearApproxTower.lean#L39-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslateStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLinearApproxTower
import Theorems.Thm_GlobalTheory_AdLat_Translate_nsmul_cancel

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

theorem GlobalTheory.AdLat.Tower.nsmul_cancel {N : ℕ} (hN : 0 < N) {z u : Fin n → RA F E} (h : N • z = N • u) : z = u := by sorry
