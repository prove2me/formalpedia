-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_discrete_dual
-- name    : GlobalTheory.UnimodOver.discrete_dual
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:21.471886+00:00
-- url     : https://prove2.me/theorems/92b81c48-8380-4be4-8e40-5fa06a0619f2
-- title:
--   Unimod Over: discrete dual
-- statement:
--   The Unimod Over construction uses the discrete dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L26-L32

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

theorem GlobalTheory.UnimodOver.discrete_dual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by sorry
