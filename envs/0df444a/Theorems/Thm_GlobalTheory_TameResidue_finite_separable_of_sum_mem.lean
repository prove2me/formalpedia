-- Prove2me | Theorems.Thm_GlobalTheory_TameResidue_finite_separable_of_sum_mem
-- name    : GlobalTheory.TameResidue.finite_separable_of_sum_mem
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:22.235899+00:00
-- url     : https://prove2.me/theorems/84abeb0d-262e-4ffd-b730-fd8a3e611d66
-- title:
--   Tame Residue: finite separable of sum mem
-- statement:
--   The Tame Residue construction uses the finite separable of sum mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L43-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L43-L89

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FiniteSeparableOfSumMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory GlobalTheory.TameResidue

theorem GlobalTheory.TameResidue.finite_separable_of_sum_mem {D k K : Type} [Group D] [Fintype D] [Field k] [Field K]
    [Algebra k K] (φ : D →* (K ≃ₐ[k] K)) (h : (Nat.card φ.ker : K) ≠ 0)
    (hT : ∀ x : K, ∃ c : k, algebraMap k K c = ∑ g, φ g x) :
    FiniteDimensional k K ∧ Algebra.IsSeparable k K := by sorry
