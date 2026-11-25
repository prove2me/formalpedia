-- Prove2me | Theorems.Thm_GlobalTheory_SmoothDedekind_exists_point_of_isMaximal
-- name    : GlobalTheory.SmoothDedekind.exists_point_of_isMaximal
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T16:05:42.333938+00:00
-- url     : https://prove2.me/theorems/fb01e52c-b853-4965-8a3d-36819884b226
-- title:
--   Smooth Dedekind: exists point of is Maximal
-- statement:
--   The Smooth Dedekind construction uses the exists point of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L32-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SmoothOfRelativeDimensionOfFlatDedekindTangentLe.lean#L32-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SpanFinrankMaximalIdealLeNcardOfLeSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfDimOfFinrankDerivatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteResidueFieldOfIsClosedOfLocallyOfFiniteTyp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SmoothOfRelativeDimensionOfFlatDedekindTangentLe
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
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.SmoothDedekind
open GlobalTheory.SmoothTangent IsLocalRing

theorem GlobalTheory.SmoothDedekind.exists_point_of_isMaximal (k : Type) [Field k] [PerfectField k] {B : Type} [CommRing B]
    [Algebra k B] [Algebra.FiniteType k B] (x : Ideal B) [x.IsMaximal] :
    ∃ (C : Type) (_ : Field C) (_ : IsAlgClosed C) (r : ℕ)
      (g : B →+* TrivSqZeroExt C (Fin r → C)), Module.finrank (B ⧸ x) x.Cotangent ≤ r ∧
      (∀ c : k, (g (algebraMap k B c)).snd = 0) ∧
      ∀ lam : (Fin r → C) →ₗ[C] C, (∀ b, lam (g b).snd = 0) → lam = 0 := by sorry
