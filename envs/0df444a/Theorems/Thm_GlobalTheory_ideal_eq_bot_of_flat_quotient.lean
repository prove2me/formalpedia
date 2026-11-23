-- Prove2me | Theorems.Thm_GlobalTheory_ideal_eq_bot_of_flat_quotient
-- name    : GlobalTheory.ideal_eq_bot_of_flat_quotient
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:07.831143+00:00
-- url     : https://prove2.me/theorems/b6443096-d21c-46ec-8e44-0c72e2f71bf3
-- title:
--   Global Theory: ideal eq bot of flat quotient
-- statement:
--   The Global Theory construction uses the ideal eq bot of flat quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L506-L525
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/IdealEqBotOfFlatQuotientOfMapMaximalIdeal.lean#L506-L525

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing

theorem GlobalTheory.ideal_eq_bot_of_flat_quotient (T : Type*) {R : Type*} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra T R] [IsLocalHom (algebraMap T R)] {J : Ideal R} (hJ : J ≠ ⊤)
    [Module.Flat T (R ⧸ J)] : J = ⊥ := by sorry
