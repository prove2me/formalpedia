-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_apply
-- name    : GlobalTheory.OppRad.S_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:24.632688+00:00
-- url     : https://prove2.me/theorems/b0015114-68f7-4227-ae8e-bbc29f4f232a
-- title:
--   Opp Rad: S apply
-- statement:
--   The Opp Rad construction uses the S apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L69-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {G V : Type} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V)

theorem GlobalTheory.OppRad.S_apply (H : Subgroup G) [Fintype H] (v : V) : S π H v = ∑ h : H, π h v := by sorry
