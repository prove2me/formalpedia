-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_PrepBd_map_pow_sub
-- name    : GlobalTheory.PMonE.PrepBd.map_pow_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:40.250074+00:00
-- url     : https://prove2.me/theorems/8a2f7607-3af7-451c-8339-c00581e2d660
-- title:
--   Prep Bd: map pow sub
-- statement:
--   The Prep Bd construction uses the map pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L66-L75

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

theorem GlobalTheory.PMonE.PrepBd.map_pow_sub (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) {A B : Matrix m m F} {ε : ℝ}
    (hA : PrepBd 1 A) (hB : PrepBd 1 B) (h : PrepBd ε (A - B)) :
    PrepBd ε (A.map (fun a => a ^ (p ^ e) ^ n) - B.map (fun a => a ^ (p ^ e) ^ n)) := by sorry
