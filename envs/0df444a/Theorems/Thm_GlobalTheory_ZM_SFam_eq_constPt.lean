-- Prove2me | Theorems.Thm_GlobalTheory_ZM_SFam_eq_constPt
-- name    : GlobalTheory.ZM.SFam.eq_constPt
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:57.916053+00:00
-- url     : https://prove2.me/theorems/364039d3-4fb3-53a3-b371-13fa4513e17e
-- title:
--   SFam: eq const Pt
-- statement:
--   The SFam construction uses the eq const Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/IsSeparatedOfIsQProjOver.lean#L79-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/IsSeparatedOfIsQProjOver.lean#L79-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_AuxiliaryInertOddPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSeparatedOfIsQProjOver
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
noncomputable section
open GlobalTheory GlobalTheory.ZM
variable {o : Type} [CommRing o] {S : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o}
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.ZM.SFam.eq_constPt {h : ℕ} {ζ : o} (F : SFam h k ζ) (K : Type) [Field K] (x : Sp (DualNumber K) ⟶ F.X)
    (c : SiegPre h k ζ (x ≫ F.s)) (hs : x ≫ F.s = constPt x ≫ F.s) (h₁ : SiegPB c F.univ x)
    (h₂ : SiegPB c F.univ (constPt x)) : x = constPt x := by sorry
