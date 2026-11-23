-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_mem_U
-- name    : GlobalTheory.OppRad.mem_U
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:05:38.590913+00:00
-- url     : https://prove2.me/theorems/754ee255-5523-4993-a675-4b631af39144
-- title:
--   Opp Rad: mem U
-- statement:
--   The Opp Rad construction uses the mem U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L31-L31

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
variable {R : Type} [Ring R]

theorem GlobalTheory.OppRad.mem_U {p q : R} {u : Rˣ} : u ∈ U p q ↔ p * (u.val - 1) = u.val - 1 ∧ (u.val - 1) * q = u.val - 1 := by sorry
