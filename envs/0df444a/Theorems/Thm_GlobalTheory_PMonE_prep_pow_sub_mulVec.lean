-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_prep_pow_sub_mulVec
-- name    : GlobalTheory.PMonE.prep_pow_sub_mulVec
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:39:29.245137+00:00
-- url     : https://prove2.me/theorems/6fc5ff7d-9f8a-482d-97fa-2073348a9a8c
-- title:
--   PMon E: prep pow sub mul Vec
-- statement:
--   The PMon E construction uses the prep pow sub mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L145-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdditiveSystemPreparationNormalFormOne.lean#L145-L152

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
omit [IsUltrametricDist F]

theorem GlobalTheory.PMonE.prep_pow_sub_mulVec (p : ℕ) [Fact p.Prime] [CharP F p] (e n : ℕ) (A : Matrix m m F) (x : m → F) :
    (fun i => (x i ^ p ^ e - A.mulVec x i) ^ (p ^ e) ^ n) =
      (fun i => x i ^ (p ^ e) ^ (n + 1)) - (A.map (fun a => a ^ (p ^ e) ^ n)).mulVec (fun i => x i ^ (p ^ e) ^ n) := by sorry
