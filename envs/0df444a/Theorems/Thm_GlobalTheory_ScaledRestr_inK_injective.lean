-- Prove2me | Theorems.Thm_GlobalTheory_ScaledRestr_inK_injective
-- name    : GlobalTheory.ScaledRestr.inK_injective
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:47:51.219946+00:00
-- url     : https://prove2.me/theorems/504cb7d7-9ac1-4869-8fa1-f1f17f170f91
-- title:
--   Scaled Restr: in K injective
-- statement:
--   The Scaled Restr construction uses the in K injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegrality.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/CmTypePeriodIntegrality.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_ConjugateOrderData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypePeriodIntegrality
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
open GlobalTheory GlobalTheory.ScaledRestr

theorem GlobalTheory.ScaledRestr.inK_injective {O : Type} [CommRing O] [IsDomain O] (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (H : Type) [AddCommGroup H] [Module O H] [Module.Free O H] : Function.Injective (inK K H : H →ₗ[O] K ⊗[O] H) := by sorry
