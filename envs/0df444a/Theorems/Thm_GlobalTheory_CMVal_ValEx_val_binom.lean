-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_val_binom
-- name    : GlobalTheory.CMVal.ValEx.val_binom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:03:37.303209+00:00
-- url     : https://prove2.me/theorems/106150fd-dbd0-4d73-89ad-ab4bb8f9ccb3
-- title:
--   Val Ex: val binom
-- statement:
--   The Val Ex construction uses the val binom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L42-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L42-L53

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

theorem GlobalTheory.CMVal.ValEx.val_binom {t : K} (ht : v t ≤ 1) (n : ℕ) : v ((1 + t) ^ n - 1 - n * t) ≤ v t * v t := by sorry
