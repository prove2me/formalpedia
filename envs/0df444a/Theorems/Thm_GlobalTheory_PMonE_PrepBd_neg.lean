-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_PrepBd_neg
-- name    : GlobalTheory.PMonE.PrepBd.neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:51.699411+00:00
-- url     : https://prove2.me/theorems/00c9cefb-63a8-4562-a2fc-380e5ffb7dba
-- title:
--   Prep Bd: neg
-- statement:
--   The Prep Bd construction uses the neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L32-L33

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
omit [Fintype m] [IsUltrametricDist F]

theorem GlobalTheory.PMonE.PrepBd.neg {c : ℝ} {X : Matrix m m F} (hX : PrepBd c X) : PrepBd c (-X) := by sorry
