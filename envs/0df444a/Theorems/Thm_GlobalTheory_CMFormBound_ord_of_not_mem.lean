-- Prove2me | Theorems.Thm_GlobalTheory_CMFormBound_ord_of_not_mem
-- name    : GlobalTheory.CMFormBound.ord_of_not_mem
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:03:05.475431+00:00
-- url     : https://prove2.me/theorems/3c3fea2b-4d11-47a7-bc55-e912f00c8d94
-- title:
--   CMForm Bound: ord of not mem
-- statement:
--   The CMForm Bound construction uses the ord of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L23-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodGaloisIntegral.lean#L23-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodGaloisIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain TensorProduct GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations
open Classical
open scoped ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.CMFormBound
variable (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {K : Type} [Field K] [Algebra O K]
  [IsFractionRing O K]

theorem GlobalTheory.CMFormBound.ord_of_not_mem (x : O) (hx : x ∉ IsLocalRing.maximalIdeal O) : ord_vw O (algebraMap O K x) = 0 := by sorry
