-- Prove2me | Theorems.Thm_GlobalTheory_BruhatRep_t_mx
-- name    : GlobalTheory.BruhatRep.t_mx
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:03:42.502676+00:00
-- url     : https://prove2.me/theorems/a9e99766-9597-43d2-9dcb-a5320aedee4c
-- title:
--   Bruhat Rep: t mx
-- statement:
--   The Bruhat Rep construction uses the t mx property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L84-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/Sl2PresentationRelations.lean#L84-L85

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
variable (n : K → M) (m : Kˣ → M) (t : M)

theorem GlobalTheory.BruhatRep.t_mx (htm : ∀ s, t * m s = m s⁻¹ * t) {x : K} (hx : x ≠ 0) : t * mx m x = mx m x⁻¹ * t := by sorry
