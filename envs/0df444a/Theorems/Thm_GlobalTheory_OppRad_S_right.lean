-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_right
-- name    : GlobalTheory.OppRad.S_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:26.709818+00:00
-- url     : https://prove2.me/theorems/b854dc91-1c75-4a25-b26f-26e432cc45ad
-- title:
--   Opp Rad: S right
-- statement:
--   The Opp Rad construction uses the S right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L84-L88

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

theorem GlobalTheory.OppRad.S_right {H : Subgroup G} {h : G} (hh : h ∈ H) (v : V) : S π H (π h v) = S π H v := by sorry
