-- Prove2me | Theorems.Thm_GlobalTheory_FiniteFlatKilled_main
-- name    : GlobalTheory.FiniteFlatKilled.main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:20.144653+00:00
-- url     : https://prove2.me/theorems/066d720b-0f5e-4b52-8f81-90b737611c01
-- title:
--   Finite Flat Killed: main
-- statement:
--   The Finite Flat Killed construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L242-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsIdPowEqOneOfIsFiniteOfFlat.lean#L242-L244

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsIdPowEqOneOfIsFiniteOfFlat
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
open GlobalTheory
open GlobalTheory.FiniteFlatKilled
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry TensorProduct WithConv
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.FiniteFlatKilled.main : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (H : Over (Spec (CommRingCat.of R)))
    [GrpObj H] [IsCommMonObj H], IsFinite H.hom → Flat H.hom → ∃ N : ℕ, 1 ≤ N ∧ 𝟙 H ^ N = 1 := by sorry
