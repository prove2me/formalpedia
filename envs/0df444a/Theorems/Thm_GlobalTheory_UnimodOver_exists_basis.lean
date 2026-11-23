-- Prove2me | Theorems.Thm_GlobalTheory_UnimodOver_exists_basis
-- name    : GlobalTheory.UnimodOver.exists_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:18:40.487902+00:00
-- url     : https://prove2.me/theorems/608aa23a-8cb7-4cbe-9310-1de97c082b21
-- title:
--   Unimod Over: exists basis
-- statement:
--   The Unimod Over construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L18-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsPolarizedSuperlatticeOfRiemannForm.lean#L18-L24

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

theorem GlobalTheory.UnimodOver.exists_basis (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by sorry
