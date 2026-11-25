-- Prove2me | Theorems.Thm_GlobalTheory_ArcTransport_gtRel_zpow
-- name    : GlobalTheory.ArcTransport.gtRel_zpow
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T18:37:43.106147+00:00
-- url     : https://prove2.me/theorems/1274f03d-f5b7-5692-9d0b-d56c207eaedc
-- title:
--   Arc Transport: gt Rel zpow
-- statement:
--   The Arc Transport construction uses the gt Rel zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L518-L522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L518-L522

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {c : Coeff l}
  {k : Type} [Field k] {bF : c.F →+* k} (a : ArcIn D l (RingHom.id c.F) k bF)
  {P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})} [Module (𝓞 E) P.toPre.X]
  {φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left} (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X)
  {F : Type} [Field F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
variable {a w e uF}

theorem GlobalTheory.ArcTransport.gtRel_zpow (h0 : uF ≠ 0) (m : a.D₀.X → ℤ) (g₀ : GtPtF a.D₀ F) (g : GtPtF P.toPre F) :
    GtRel w e.toAddEquiv (fun z => Units.mk0 uF h0 ^ m z) g₀ g ↔
      ∀ z, GenRel w (g.s (e z)) (g₀.s z) (uF ^ m z) := by sorry
