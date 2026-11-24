-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_PrepBd_mono
-- name    : GlobalTheory.PMonE.PrepBd.mono
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:38:26.600392+00:00
-- url     : https://prove2.me/theorems/70401c0a-5715-468c-8e17-d4d27ccce249
-- title:
--   Prep Bd: mono
-- statement:
--   The Prep Bd construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L36-L37

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

theorem GlobalTheory.PMonE.PrepBd.mono {c d : ℝ} {X : Matrix m m F} (hX : PrepBd c X) (h : c ≤ d) : PrepBd d X := by sorry
