-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_mem_torsion_iff
-- name    : GroundTheory.Global.Cyclotomic.mem_torsion_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:26:48.119533+00:00
-- url     : https://prove2.me/theorems/49bfa1dc-529e-43ab-a4f4-cf8c8d17edc2
-- title:
--   Cyclotomic: mem torsion iff
-- statement:
--   The Cyclotomic construction uses the mem torsion iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/PadicUnitsLog.lean#L382-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/PadicUnitsLog.lean#L382-L384

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

theorem GroundTheory.Global.Cyclotomic.mem_torsion_iff (u : ℤ_[ℓ]ˣ) :
    u ∈ CommGroup.torsion ℤ_[ℓ]ˣ ↔ u ^ torsionExponent ℓ = 1 := by sorry
