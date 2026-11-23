-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_eq_zero_of_S
-- name    : GlobalTheory.OppRad.eq_zero_of_S
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:19.703532+00:00
-- url     : https://prove2.me/theorems/a9b03c54-2a56-43bb-847d-e62177c06dc5
-- title:
--   Opp Rad: eq zero of S
-- statement:
--   The Opp Rad construction uses the eq zero of S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L104-L107

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
variable {π}

theorem GlobalTheory.OppRad.eq_zero_of_S {H : Subgroup G} {v : V} (hv : ∀ h ∈ H, π h v = v) (h0 : S π H v = 0) : v = 0 := by sorry
