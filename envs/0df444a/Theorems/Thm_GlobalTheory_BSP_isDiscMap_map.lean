-- Prove2me | Theorems.Thm_GlobalTheory_BSP_isDiscMap_map
-- name    : GlobalTheory.BSP.isDiscMap_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:49:44.492491+00:00
-- url     : https://prove2.me/theorems/e3af5b91-8c9e-42e7-997a-c425d5a65fb7
-- title:
--   BSP: is Disc Map map
-- statement:
--   The BSP construction uses the is Disc Map map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L322-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemBallOfGaugeLt.lean#L322-L346

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemBallOfGaugeLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped NNReal
open GlobalTheory GlobalTheory.BSP
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}
open scoped NNReal
variable (l : ℕ) {A : Type} [CommRing A] (u : A) (ρ : ℝ≥0)
variable {l u ρ} {A' : Type} [CommRing A'] {u' : A'} {ρ' : ℝ≥0}

theorem GlobalTheory.BSP.isDiscMap_map [Fact l.Prime] (f : A →+* A')
    (h : ‖_root_.GlobalTheory.BSP.toDisc l u' ρ' (f u)‖ ≤ ρ) :
    _root_.GlobalTheory.BSP.IsDiscMap f (_root_.GlobalTheory.BSP.Disc.map f h) := by sorry
