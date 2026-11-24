-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_matrix_regular
-- name    : GlobalTheory.OppRad.matrix_regular
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:40:19.451015+00:00
-- url     : https://prove2.me/theorems/41bbfe84-b528-483f-a676-6b8924505943
-- title:
--   Opp Rad: matrix regular
-- statement:
--   The Opp Rad construction uses the matrix regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L252-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L252-L264

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
variable {R V : Type} [Ring R] [Finite R] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ Rˣ V}

theorem GlobalTheory.OppRad.matrix_regular {F n : Type} [Field F] [Fintype n] [DecidableEq n] (x : Matrix n n F) :
    ∃ y, x * y * x = x := by sorry
