-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_PrepBd_add
-- name    : GlobalTheory.PMonE.PrepBd.add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:15.284612+00:00
-- url     : https://prove2.me/theorems/4954c1d1-6531-49a2-8926-9d8d53802fca
-- title:
--   Prep Bd: add
-- statement:
--   The Prep Bd construction uses the add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L28-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L28-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdditiveSystemPreparationNormalFormOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PMonE
open Finset
variable {F : Type} [NormedField F] {m : Type} [Fintype m]
variable [IsUltrametricDist F]
omit [Fintype m]

theorem GlobalTheory.PMonE.PrepBd.add {c : ℝ} {X Y : Matrix m m F} (hX : PrepBd c X) (hY : PrepBd c Y) : PrepBd c (X + Y) := by sorry
