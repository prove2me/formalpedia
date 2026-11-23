-- Prove2me | Theorems.Thm_GlobalTheory_LocDerExt_der_exists
-- name    : GlobalTheory.LocDerExt.der_exists
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:38:48.470998+00:00
-- url     : https://prove2.me/theorems/cc841675-c5e3-42e5-98df-f401f0287876
-- title:
--   Loc Der Ext: der exists
-- statement:
--   The Loc Der Ext construction uses the der exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L28-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsLocalDerivationExtensionOfAffine.lean#L28-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
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
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
open GlobalTheory GlobalTheory.LocDerExt

theorem GlobalTheory.LocDerExt.der_exists {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra A B] (f : A)
    [IsLocalization.Away f B] (φ : B →+* C) (d : A → C)
    (hadd : ∀ a b, d (a + b) = d a + d b)
    (hmul : ∀ a b, d (a * b) = φ (algebraMap A B a) * d b + φ (algebraMap A B b) * d a) :
    ∃ δ : B → C, (∀ a b, δ (a + b) = δ a + δ b) ∧ (∀ a b, δ (a * b) = φ a * δ b + φ b * δ a) ∧
      ∀ a, δ (algebraMap A B a) = d a := by sorry
