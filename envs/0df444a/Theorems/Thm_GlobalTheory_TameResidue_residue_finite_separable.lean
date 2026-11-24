-- Prove2me | Theorems.Thm_GlobalTheory_TameResidue_residue_finite_separable
-- name    : GlobalTheory.TameResidue.residue_finite_separable
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:02:19.346101+00:00
-- url     : https://prove2.me/theorems/cb5c45d4-68da-47ed-b6e2-965780b5d564
-- title:
--   Tame Residue: residue finite separable
-- statement:
--   The Tame Residue construction uses the residue finite separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L126-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/FiniteSeparableOfSumMem.lean#L126-L273

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

theorem GlobalTheory.TameResidue.residue_finite_separable : ∀ (Γ : Type) [Group Γ] [Finite Γ] (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction Γ B] [SMulCommClass Γ A B] [Algebra.IsInvariant A B Γ] (q : Ideal B) [q.IsPrime] (k K : Type) [Field k] [Field K] [Algebra (A ⧸ q.under A) k] [IsFractionRing (A ⧸ q.under A) k] [Algebra (B ⧸ q) K] [IsFractionRing (B ⧸ q) K] [Algebra k K], (∀ a : A, algebraMap k K (algebraMap (A ⧸ q.under A) k (Ideal.Quotient.mk _ a)) = algebraMap (B ⧸ q) K (Ideal.Quotient.mk q (algebraMap A B a))) → (Nat.card (q.inertia Γ) : B) ∉ q → FiniteDimensional k K ∧ Algebra.IsSeparable k K := by sorry
