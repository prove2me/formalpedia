-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_en_mS
-- name    : GlobalTheory.BruhatRep.en_mS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:51.432018+00:00
-- url     : https://prove2.me/theorems/c8299a5f-0b11-435d-9b04-e0161fdd027b
-- title:
--   Bruhat Rep: en m S
-- statement:
--   The Bruhat Rep construction uses the en m S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L24-L25

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_Sl2PresentationRelations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.BruhatRep
variable {K : Type} [Field K]

theorem GlobalTheory.BruhatRep.en_mS (s : Kˣ) : en (mS s) 0 0 = s ∧ en (mS s) 0 1 = 0 ∧ en (mS s) 1 0 = 0 ∧ en (mS s) 1 1 = (s : K)⁻¹ := by sorry
