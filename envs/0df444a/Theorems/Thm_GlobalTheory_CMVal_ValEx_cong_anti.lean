-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_cong_anti
-- name    : GlobalTheory.CMVal.ValEx.cong_anti
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:06:30.262822+00:00
-- url     : https://prove2.me/theorems/247ec790-3fd4-4a2d-97c7-9363f4cf5695
-- title:
--   Val Ex: cong anti
-- statement:
--   The Val Ex construction uses the cong anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L29-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsUnitaryCharOfOpenSubgroupAndHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_WithZeroEqOfLeExpIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
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
open scoped WithZero
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.ValEx
variable {K : Type} [Field K] (v : Valuation K ℤᵐ⁰)

theorem GlobalTheory.CMVal.ValEx.cong_anti {m n : ℕ} (h : m ≤ n) : cong v n ≤ cong v m := by sorry
