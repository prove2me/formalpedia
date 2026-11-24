-- Prove2me | Theorems.Thm_GlobalTheory_CoverGlue_exists_fac_field
-- name    : GlobalTheory.CoverGlue.exists_fac_field
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T12:27:35.728803+00:00
-- url     : https://prove2.me/theorems/2aa9f3aa-1452-472a-b2f1-b48f90562fb9
-- title:
--   Cover Glue: exists fac field
-- statement:
--   The Cover Glue construction uses the exists fac field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionBasisGeometricFibresOfOpenCover.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/TorsionBasisGeometricFibresOfOpenCover.lean#L14-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TorsionBasisGeometricFibresOfOpenCover
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
open GlobalTheory GlobalTheory.CoverGlue

theorem GlobalTheory.CoverGlue.exists_fac_field {S : Scheme.{0}} {I : Type} {U : I → S.Opens} (hU : iSup U = ⊤) (K : Type) [Field K]
    (x : Sp K ⟶ S) : ∃ (i : I) (x' : Sp K ⟶ (U i).toScheme), x' ≫ (U i).ι = x := by sorry
