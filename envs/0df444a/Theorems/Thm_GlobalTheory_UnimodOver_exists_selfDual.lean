-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_exists_selfDual
-- name    : GlobalTheory.UnimodOver.exists_selfDual
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:25:31.294721+00:00
-- url     : https://prove2.me/theorems/f90a549d-2912-465b-8abd-a818d49750fa
-- title:
--   Unimod Over: exists self Dual
-- statement:
--   The Unimod Over construction uses the exists self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L56-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L56-L99

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

theorem GlobalTheory.UnimodOver.exists_selfDual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by sorry
