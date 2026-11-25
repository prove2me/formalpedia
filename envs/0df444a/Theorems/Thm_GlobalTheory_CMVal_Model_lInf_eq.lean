-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_lInf_eq
-- name    : GlobalTheory.CMVal.Model.lInf_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:06.701424+00:00
-- url     : https://prove2.me/theorems/af2ce920-2d31-43fc-b7e3-df03fe5b01f7
-- title:
--   Model: l Inf eq
-- statement:
--   The Model construction uses the l Inf eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L134-L136

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
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

theorem GlobalTheory.CMVal.Model.lInf_eq {I : Type} [Fintype I] (m : I → ℤ) (s : ℂ) :
    LInf m s = ∏ i, Complex.Gammaℂ (s + (|m i| : ℤ)) := by sorry
