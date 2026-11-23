-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_imForm_apply
-- name    : GlobalTheory.UnimodOver.imForm_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:37.870134+00:00
-- url     : https://prove2.me/theorems/b91bc043-087c-4185-b14f-23f6753e802e
-- title:
--   Unimod Over: im Form apply
-- statement:
--   The Unimod Over construction uses the im Form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L155-L156

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPolarizedSuperlatticeOfRiemannForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.UnimodOver
open Module

theorem GlobalTheory.UnimodOver.imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := by sorry
