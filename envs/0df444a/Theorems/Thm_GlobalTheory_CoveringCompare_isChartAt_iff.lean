-- Prove2me | Theorems.Thm_GlobalTheory_CoveringCompare_isChartAt_iff
-- name    : GlobalTheory.CoveringCompare.isChartAt_iff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:47:08.689886+00:00
-- url     : https://prove2.me/theorems/a5087d2f-d715-4194-9db0-bec53e553ad7
-- title:
--   Covering Compare: is Chart At iff
-- statement:
--   The Covering Compare construction uses the is Chart At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L61-L64

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SABBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAndSmoothness
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_CoveringAbelianLocusSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsFiniteTorusExtensionOfModel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitExtIsGtOfTorusExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CoveringAndSmoothnessIffOfSeparableSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CoveringCompare
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem GlobalTheory.CoveringCompare.isChartAt_iff (Y : Model Xo c β) (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (ξ : Sp R ⟶ Y.X) :
    CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x := by sorry
