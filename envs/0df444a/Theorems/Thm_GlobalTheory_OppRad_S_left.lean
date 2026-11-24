-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_left
-- name    : GlobalTheory.OppRad.S_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:10:56.702349+00:00
-- url     : https://prove2.me/theorems/4aea52c0-2d6c-4f59-8179-09217b0bce30
-- title:
--   Opp Rad: S left
-- statement:
--   The Opp Rad construction uses the S left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L90-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L90-L92

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

theorem GlobalTheory.OppRad.S_left {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : π h (S π H v) = S π H v := by sorry
