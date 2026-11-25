-- Prove2me | Theorems.Thm_GlobalTheory_ArcTransport_exists_commonField
-- name    : GlobalTheory.ArcTransport.exists_commonField
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T18:29:04.173949+00:00
-- url     : https://prove2.me/theorems/96d28732-b15b-5e93-b757-7c5fa1479415
-- title:
--   Arc Transport: exists common Field
-- statement:
--   The Arc Transport construction uses the exists common Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L666-L675
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L666-L675

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ArcTransport
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ToricData GlobalTheory.HostModel
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l)
  (k : Type) [Field k] (bF : c.F →+* k)

theorem GlobalTheory.ArcTransport.exists_commonField : ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F)
    (_ : Algebra (FractionRing (PowerSeries k)) F) (_ : Algebra (FractionRing k) F),
    ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)) := by sorry
