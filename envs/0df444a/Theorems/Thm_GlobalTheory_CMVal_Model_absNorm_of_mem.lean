-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_absNorm_of_mem
-- name    : GlobalTheory.CMVal.Model.absNorm_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:01:28.211711+00:00
-- url     : https://prove2.me/theorems/d0085a55-bd56-43c1-95be-cee7ce2ba2d3
-- title:
--   Model: abs Norm of mem
-- statement:
--   The Model construction uses the abs Norm of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L309-L322
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L309-L322

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

theorem GlobalTheory.CMVal.Model.absNorm_of_mem (P : HeightOneSpectrum (𝓞 K)) (h : ((43 : ℕ) : 𝓞 K) ∈ P.asIdeal) : Ideal.absNorm P.asIdeal = 43 := by sorry
