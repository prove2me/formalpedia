-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_torsion_two_iff
-- name    : GroundTheory.Global.Cyclotomic.mem_torsion_two_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:56:18.514022+00:00
-- url     : https://prove2.me/theorems/8e24c769-bf94-4606-ab54-0a332761ec1f
-- title:
--   Cyclotomic: mem torsion two iff
-- statement:
--   The Cyclotomic construction uses the mem torsion two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/PadicUnitsLog.lean#L386-L396
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/PadicUnitsLog.lean#L386-L396

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_PadicUnitsLog
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
variable (ℓ : ℕ) [hℓ : Fact ℓ.Prime]

theorem GroundTheory.Global.Cyclotomic.mem_torsion_two_iff (u : ℤ_[2]ˣ) :
    u ∈ CommGroup.torsion ℤ_[2]ˣ ↔ u = 1 ∨ u = -1 := by sorry
