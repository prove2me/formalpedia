-- Prove2me | Theorems.Thm_GlobalTheory_UnitValueExistence_main
-- name    : GlobalTheory.UnitValueExistence.main
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:39:06.958818+00:00
-- url     : https://prove2.me/theorems/aaf4092b-b2dd-4d4c-980f-0c6510da0867
-- title:
--   Unit Value Existence: main
-- statement:
--   The Unit Value Existence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormOneAddEqOne.lean#L97-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormOneAddEqOne.lean#L97-L99

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormOneAddEqOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UnitValueExistence
open Matrix

theorem GlobalTheory.UnitValueExistence.main : (let d1 : {E : Type} → [NormedField E] → {n m : Type} → Matrix n m E → Prop := @(fun {E : Type} [NormedField E] {n m : Type} (h : Matrix n m E) ↦ ∀ (i : n) (j : m), ‖h i j‖ ≤ (1 : ℝ)); ∀ {E : Type} [inst : NormedField E] [IsUltrametricDist E] [inst_2 : StarRing E], (∀ (y : E), ‖Star.star y‖ = ‖y‖) → ∀ (e0 : E), ‖e0‖ ≤ (1 : ℝ) → e0 + Star.star e0 = (1 : E) → ∀ {n : Type} [inst_3 : Fintype n] [inst_4 : DecidableEq n] [Nonempty n] (G : Matrix n n E), Matrix.IsHermitian G → d1 G → ‖Matrix.det G‖ = (1 : ℝ) → ∃ (i : n) (w : n → E), (∀ (a : n), ‖w a‖ ≤ (1 : ℝ)) ∧ w i = (1 : E) ∧ ‖Star.star w ⬝ᵥ Matrix.mulVec G w‖ = (1 : ℝ)) := by sorry
