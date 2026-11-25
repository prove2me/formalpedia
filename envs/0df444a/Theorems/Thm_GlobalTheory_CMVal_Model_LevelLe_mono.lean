-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_LevelLe_mono
-- name    : GlobalTheory.CMVal.Model.LevelLe.mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:36.483855+00:00
-- url     : https://prove2.me/theorems/bc1374a4-9917-4d68-9fb7-57d461b6db04
-- title:
--   Level Le: mono
-- statement:
--   The Level Le construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L144-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L144-L146

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_QNorm_admitted_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.Model.LevelLe.mono {χ : HChar E} {P : HeightOneSpectrum (𝓞 E)} {m n : ℕ} (h : LevelLe χ P m) (hmn : m ≤ n) :
    LevelLe χ P n := by sorry
