-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_span_of_le
-- name    : GlobalTheory.UnimodOver.span_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:00:30.883851+00:00
-- url     : https://prove2.me/theorems/e71d09b9-6514-4855-8ea2-9b828ffea3e3
-- title:
--   Unimod Over: span of le
-- statement:
--   The Unimod Over construction uses the span of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L38-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L38-L41

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
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem GlobalTheory.UnimodOver.span_of_le {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by sorry
