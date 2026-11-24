-- Prove2me | Theorems.Thm_GlobalTheory_JR_wS_nS_wS_eq_unit
-- name    : GlobalTheory.JR.wS_nS_wS_eq_unit
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T17:41:01.506386+00:00
-- url     : https://prove2.me/theorems/b54e5c4c-2aac-43b8-b14e-67d084731aeb
-- title:
--   JR: w S n S w S eq unit
-- statement:
--   The JR construction uses the w S n S w S eq unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerFunctionalWeylVanishOfWeylUnipotentZero.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WhittakerFunctionalWeylVanishOfWeylUnipotentZero.lean#L7-L18

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleHermitianPairStructureFactsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WhittakerFunctionalWeylVanishOfWeylUnipotentZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR

theorem GlobalTheory.JR.wS_nS_wS_eq_unit {k : Type} [CommRing k] (z : kˣ) :
    wS k * nS (z : k) * wS k = nS ((-z⁻¹ : kˣ) : k) * mS (-z⁻¹) * (wS k * nS ((-z⁻¹ : kˣ) : k)) := by sorry
