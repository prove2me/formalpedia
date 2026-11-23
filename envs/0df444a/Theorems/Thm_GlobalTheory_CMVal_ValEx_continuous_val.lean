-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_ValEx_continuous_val
-- name    : GlobalTheory.CMVal.ValEx.continuous_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:22.292967+00:00
-- url     : https://prove2.me/theorems/fac29bf0-94ac-4624-becd-568710da3dd4
-- title:
--   Val Ex: continuous val
-- statement:
--   The Val Ex construction uses the continuous val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousOfVal.lean#L134-L135

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
variable {E : Type} [Field E] [NumberField E]
open WithZeroTopology

theorem GlobalTheory.CMVal.ValEx.continuous_val (w : HeightOneSpectrum (𝓞 E)) : Continuous fun x : w.adicCompletion E => Valued.v x := by sorry
