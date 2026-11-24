-- Prove2me | Theorems.Thm_GlobalTheory_KS_VertFib_comp_eq_const
-- name    : GlobalTheory.KS.VertFib.comp_eq_const
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:47:54.582262+00:00
-- url     : https://prove2.me/theorems/8be0b9a8-bb0c-423b-8034-ca8ca046ae2c
-- title:
--   Vert Fib: comp eq const
-- statement:
--   The Vert Fib construction uses the comp eq const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationOfFibreOfKillsBase.lean#L84-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GermDerivationOfFibreOfKillsBase.lean#L84-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationIffDualNumberPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GermDerivationOfFibreOfKillsBase
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
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.VertFib

theorem GlobalTheory.KS.VertFib.comp_eq_const {R : Type} [CommRing R] (x₀ : R →+* ℂ) {X : Scheme.{0}} (p : X ⟶ Sp R)
    (v : Sp (DualNumber ℂ) ⟶ X) (h₁ : epsPt ≫ v ≫ p = spMap x₀)
    (h₂ : ∀ r, TrivSqZeroExt.snd (ringVal v ⊤ le_top (constFn p ⊤ r)) = 0) :
    v ≫ p = epsStr ≫ spMap x₀ := by sorry
