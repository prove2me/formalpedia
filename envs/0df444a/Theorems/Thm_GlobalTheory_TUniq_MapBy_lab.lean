-- Prove2me | Theorems.Thm_GlobalTheory_TUniq_MapBy_lab
-- name    : GlobalTheory.TUniq.MapBy.lab
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:27:09.099074+00:00
-- url     : https://prove2.me/theorems/7ad33d81-ff0f-4894-88b3-d314bc60b9a1
-- title:
--   Map By: lab
-- statement:
--   The Map By construction uses the lab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SecCoordOfRatio.lean#L67-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsCompatOfLocal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSegreCoordinates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SecCoordOfRatio
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
noncomputable section
open GlobalTheory GlobalTheory.TUniq
open GlobalTheory.SegreCoord ReciprocityTheory.ChartRestriction.G.Out
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {S S' : Scheme.{0}} {s : S ⟶ Sp o}
  {s' : S' ⟶ Sp o}

theorem GlobalTheory.TUniq.MapBy.lab {u : TObj g (N' ^ 2) J b s'} {t : TObj g (N' ^ 2) J b s} {f : S' ⟶ S} {φ : u.A.left ⟶ t.A.left}
    (h : MapBy u t f φ) (a : Ix g (N' ^ 2)) : f ≫ (t.lab a).left = (u.lab a).left ≫ φ := by sorry
