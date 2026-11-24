-- Prove2me | Theorems.Thm_GlobalTheory_TameResidue_exists_not_mem_smul_mem
-- name    : GlobalTheory.TameResidue.exists_not_mem_smul_mem
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:24.806666+00:00
-- url     : https://prove2.me/theorems/d01e2dcc-1ad5-42a5-b417-f8958a82a03b
-- title:
--   Tame Residue: exists not mem smul mem
-- statement:
--   The Tame Residue construction uses the exists not mem smul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L91-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L91-L124

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

theorem GlobalTheory.TameResidue.exists_not_mem_smul_mem {Γ B : Type} [Group Γ] [Finite Γ] [CommRing B]
    [MulSemiringAction Γ B] (q : Ideal B) [q.IsPrime] :
    ∃ y : B, y ∉ q ∧ ∀ g : Γ, g • q ≠ q → g • y ∈ q := by sorry
