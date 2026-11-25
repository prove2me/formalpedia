-- Prove2me | Theorems.Thm_GlobalTheory_NormGlue_valF_eq_of_gm
-- name    : GlobalTheory.NormGlue.valF_eq_of_gm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T15:27:59.78878+00:00
-- url     : https://prove2.me/theorems/efec7ad6-d464-5255-a193-9f5629fe9522
-- title:
--   Norm Glue: val F eq of gm
-- statement:
--   The Norm Glue construction uses the val F eq of gm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsLineBundleOfNormOneGenerators.lean#L94-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_CompanionTheory
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_RegularOfBoundedAtPadicAlgClPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsLineBundleOfNormOneGenerators
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ
open GlobalTheory
open GlobalTheory.NormGlue

theorem GlobalTheory.NormGlue.valF_eq_of_gm {F : Type} [Field F] {X X' : Scheme.{0}} {x : Sp F ⟶ X} {x' : Sp F ⟶ X'}
    {U : X.Opens} {U' : X'.Opens} (z : Sp F) (h : x z ∈ U) (h' : x' z ∈ U') {u : Γ(X, U)ˣ} {u' : Γ(X', U')ˣ}
    (e : gm x z U u = gm x' z U' u') : valF x U u.val = valF x' U' u'.val := by sorry
