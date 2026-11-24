-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_inv_rel
-- name    : GlobalTheory.OppRad.inv_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:02.333075+00:00
-- url     : https://prove2.me/theorems/f4bfa553-87f4-40af-a86b-3a9c5f614bc3
-- title:
--   Opp Rad: inv rel
-- statement:
--   The Opp Rad construction uses the inv rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L52-L53

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

theorem GlobalTheory.OppRad.inv_rel {p p' : R} {w : Rˣ} (hp : w.val * p' = p * w.val) : (w⁻¹).val * p = p' * (w⁻¹).val := by sorry
