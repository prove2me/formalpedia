-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleIdeal_ordAt_eventually
-- name    : GlobalTheory.CMVal.IdeleIdeal.ordAt_eventually
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:29.745969+00:00
-- url     : https://prove2.me/theorems/7d619637-fa6f-4dae-9f80-bb2c74e2c469
-- title:
--   Idele Ideal: ord At eventually
-- statement:
--   The Idele Ideal construction uses the ord At eventually property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsIdealSectionIntegralFiniteIdeleUpToUnits.lean#L18-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleIdeal
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.IdeleIdeal.ordAt_eventually (y : (Af E)ˣ) : ∀ᶠ w in Filter.cofinite, ordAt y w = 0 := by sorry
