-- Prove2me | Theorems.Thm_GlobalTheory_linearIndependent_of_comm_smul
-- name    : GlobalTheory.linearIndependent_of_comm_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:43:23.005596+00:00
-- url     : https://prove2.me/theorems/ebd2b653-1422-4300-8a37-182db138c5bd
-- title:
--   Global Theory: linear Independent of comm smul
-- statement:
--   The Global Theory construction uses the linear Independent of comm smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LinearIndependentOfCommSmul.lean#L12-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/LinearIndependentOfCommSmul.lean#L12-L65

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_LinearIndependentOfCommSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.linearIndependent_of_comm_smul {K G V : Type} [Field K] [AddCommGroup V] [Module K V]
    [Nontrivial V] (A : G → V →ₗ[K] V) (c : G → G → K) (hA : ∀ x, Function.Injective (A x))
    (h : ∀ x y v, A x (A y v) = c x y • A y (A x v)) (hc : Function.Injective c) :
    LinearIndependent K A := by sorry
