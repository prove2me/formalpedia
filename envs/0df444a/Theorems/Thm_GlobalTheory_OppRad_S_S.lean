-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_S
-- name    : GlobalTheory.OppRad.S_S
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:05.219812+00:00
-- url     : https://prove2.me/theorems/8b9f8215-6c7f-4409-bb01-ab38d05d616a
-- title:
--   Opp Rad: S S
-- statement:
--   The Opp Rad construction uses the S S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L99-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L99-L102

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

theorem GlobalTheory.OppRad.S_S {H K : Subgroup G} (hle : H ≤ K) {v : V} (hv : S π K v = 0) : S π K (S π H v) = 0 := by sorry
