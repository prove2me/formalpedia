-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_PrepBd_map_pow
-- name    : GlobalTheory.PMonE.PrepBd.map_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:35.529273+00:00
-- url     : https://prove2.me/theorems/a9065151-1891-4ea5-a018-8c995971aab6
-- title:
--   Prep Bd: map pow
-- statement:
--   The Prep Bd construction uses the map pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L48-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L48-L51

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

theorem GlobalTheory.PMonE.PrepBd.map_pow {X : Matrix m m F} (hX : PrepBd 1 X) (N : ℕ) : PrepBd 1 (X.map (fun a => a ^ N)) := by sorry
