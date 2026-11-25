-- Prove2me | Theorems.Thm_GlobalTheory_SharpRel_push_inj
-- name    : GlobalTheory.SharpRel.push_inj
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:23:28.796586+00:00
-- url     : https://prove2.me/theorems/9812cfab-54c8-5017-9234-ea37dac396d6
-- title:
--   Sharp Rel: push inj
-- statement:
--   The Sharp Rel construction uses the push inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SharpRelations.lean#L22-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SharpRelations.lean#L22-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SharpRelations
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
open GlobalTheory.ZM GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.SharpRel
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'}
  [GrpObj A] [GrpObj A'] {φ : A'.left ⟶ A.left}

theorem GlobalTheory.SharpRel.push_inj (h : IsGrpPullback A' A f φ) {T : Over S'} {x y : T ⟶ A'}
    (e : pushHom h T x = pushHom h T y) : x = y := by sorry
