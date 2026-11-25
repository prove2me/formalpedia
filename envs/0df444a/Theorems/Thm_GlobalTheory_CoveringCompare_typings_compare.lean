-- Prove2me | Theorems.Thm_GlobalTheory_CoveringCompare_typings_compare
-- name    : GlobalTheory.CoveringCompare.typings_compare
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T15:54:53.836638+00:00
-- url     : https://prove2.me/theorems/2b971e09-f9ee-5082-be19-42194eb81e65
-- title:
--   Covering Compare: typings compare
-- statement:
--   The Covering Compare construction uses the typings compare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L116-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/CoveringAndSmoothnessIffOfSeparableSplitting.lean#L116-L134

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

theorem GlobalTheory.CoveringCompare.typings_compare :
    (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
      (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : ℕ),
      (∀ (x : Y.X) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ Y.X),
        CoveringAbelianLocusSmooth.IsChartAt Y x R ξ ↔ UniformizationBase.IsUnifBase Y R ξ ∧ ξ (IsLocalRing.closedPoint R) = x) ∧
      ((∀ x, UniformizationBase.CovAt Y p x) ↔ CoveringAbelianLocusSmooth.CoveredByCharts Y p) ∧
      (UniformizationBase.AbLocusSmooth Y ↔ CoveringAbelianLocusSmooth.AbLocusSmooth Y) ∧ (UniformizationBase.GoodPrime l p ↔ CoveringAbelianLocusSmooth.GoodPrime l p) ∧
      (Y.SplitFibres ↔ ∀ x : Y.X, ¬ PerfectField (Y.X.residueField x) →
        ∃ (k : Type) (_ : Field k) (_ : Algebra (Y.X.residueField x) k),
          FiniteDimensional (Y.X.residueField x) k ∧ Algebra.IsSeparable (Y.X.residueField x) k ∧
            SplitOver Y.t.G x k)) ∧
    (UniformizationBase.SmoothnessLemma ↔ CoveringAbelianLocusSmooth.SmoothnessLemma) ∧
    (CoveringAbelianLocusSmooth.CoveringAndSmoothness ↔ CoveringForSplitFibres ∧ UniformizationBase.SmoothnessLemma) ∧
    (UniformizationBase.CoveringAndSmoothness → CoveringAbelianLocusSmooth.CoveringAndSmoothness) := by sorry
