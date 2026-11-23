-- Prove2me | Theorems.Thm_GlobalTheory_PlaceModel_IsBichar_nsmul
-- name    : GlobalTheory.PlaceModel.IsBichar.nsmul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:29:13.616261+00:00
-- url     : https://prove2.me/theorems/4d0e5e7f-307b-4737-925b-1183d56da4c3
-- title:
--   Is Bichar: nsmul
-- statement:
--   The Is Bichar construction uses the nsmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LinearIndependentWave.lean#L46-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/LinearIndependentWave.lean#L46-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
variable {χ : G → G → ℂ} {X Y L L' : AddSubgroup G}

theorem GlobalTheory.PlaceModel.IsBichar.nsmul (h : IsBichar χ) (k : ℕ) (x y : G) : χ (k • x) y = χ x (k • y) := by sorry
