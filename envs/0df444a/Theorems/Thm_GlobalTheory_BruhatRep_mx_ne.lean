-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_mx_ne
-- name    : GlobalTheory.BruhatRep.mx_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:01:10.386803+00:00
-- url     : https://prove2.me/theorems/bacd19d5-edab-4b59-b949-0704069a55c3
-- title:
--   Bruhat Rep: mx ne
-- statement:
--   The Bruhat Rep construction uses the mx ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L36-L37

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
variable {M : Type} [Monoid M]

theorem GlobalTheory.BruhatRep.mx_ne (m : Kˣ → M) {x : K} (hx : x ≠ 0) : mx m x = m (Units.mk0 x hx) := by sorry
