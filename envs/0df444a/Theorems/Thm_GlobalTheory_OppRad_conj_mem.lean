-- Prove2me | Theorems.Thm_GlobalTheory_OppRad_conj_mem
-- name    : GlobalTheory.OppRad.conj_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:06:30.15652+00:00
-- url     : https://prove2.me/theorems/01f3995d-ac3a-48f4-8726-86ca015cb004
-- title:
--   Opp Rad: conj mem
-- statement:
--   The Opp Rad construction uses the conj mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L41-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MatrixRegular.lean#L41-L50

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

theorem GlobalTheory.OppRad.conj_mem {p q p' q' : R} {w u : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val)
    (hu : u ∈ U p' q') : w * u * w⁻¹ ∈ U p q := by sorry
