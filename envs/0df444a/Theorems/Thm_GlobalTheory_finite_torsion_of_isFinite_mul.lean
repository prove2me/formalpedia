-- Prove2me | Theorems.Thm_GlobalTheory_finite_torsion_of_isFinite_mul
-- name    : GlobalTheory.finite_torsion_of_isFinite_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:32:07.496943+00:00
-- url     : https://prove2.me/theorems/ab1133e2-b44c-4d9e-a137-38b41e138fe1
-- title:
--   Global Theory: finite torsion of is Finite mul
-- statement:
--   The Global Theory construction uses the finite torsion of is Finite mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/HasEnoughRootsOfUnityGlobalSections.lean#L63-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/HasEnoughRootsOfUnityGlobalSections.lean#L63-L77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_HasEnoughRootsOfUnityGlobalSections
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

theorem GlobalTheory.finite_torsion_of_isFinite_mul (K : Type) [Field K] [IsAlgClosed K]
    (P : PolAV (Spec (CommRingCat.of K))) (N : ℕ) [IsFinite (mulA P.A N).left] :
    Finite {x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A // x ^ N = 1} := by sorry
