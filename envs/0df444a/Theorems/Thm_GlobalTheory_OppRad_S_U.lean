-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_S_U
-- name    : GlobalTheory.OppRad.S_U
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:15.232902+00:00
-- url     : https://prove2.me/theorems/d6c1787f-3b88-40fa-b318-8531831f0591
-- title:
--   Opp Rad: S U
-- statement:
--   The Opp Rad construction uses the S U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L113-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L113-L115

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

theorem GlobalTheory.OppRad.S_U {p q p' q' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val) (v : V) :
    π w (S π (U p' q') v) = S π (U p q) (π w v) := by sorry
