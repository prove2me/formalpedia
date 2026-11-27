-- Prove2me | Theorems.Thm_GlobalTheory_ArcTransport_genRel_val
-- name    : GlobalTheory.ArcTransport.genRel_val
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T18:25:26.045266+00:00
-- url     : https://prove2.me/theorems/28d867fa-1b68-483f-8fa9-8b28613e11a3
-- title:
--   Arc Transport: gen Rel val
-- statement:
--   The Arc Transport construction uses the gen Rel val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L63-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L63-L101

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
variable {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {Φ : X' ⟶ X} {K : Type} [Fintype K]
variable {F : Type} [Field F]

theorem GlobalTheory.ArcTransport.genRel_val {w : LB.Iso L' (L.pull Φ)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {pt : K → (Sp F ⟶ X')}
    {pt₀ : K → (Sp F ⟶ X)} {ε : K → ℤ} {t : LB.Gen (LB.LinComb L' pt ε)} {t₀ : LB.Gen (LB.LinComb L pt₀ ε)}
    (ht : t.IsGen) (ht₀ : t₀.IsGen) (x : Fˣ) :
    GenRel w t t₀ (x : F) ↔ (∀ k, pt k ≫ Φ = pt₀ k) ∧ ∀ (y : Sp F) J J', Good L y J → Good L' y J' →
      (∏ k, Geo.Tor.gw w (pt k) y (J (pt k ≫ Φ)) (J' (pt k)) ^ ε k) * vS t y J' = unitStk y x * vS t₀ y J := by sorry
