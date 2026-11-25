-- Prove2me | Theorems.Thm_GlobalTheory_ArcTransport_transport
-- name    : GlobalTheory.ArcTransport.transport
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T18:26:53.045615+00:00
-- url     : https://prove2.me/theorems/987c4b1e-d7fa-57a7-b143-14ce614a9f18
-- title:
--   Arc Transport: transport
-- statement:
--   The Arc Transport construction uses the transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L616-L640
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsCommonField.lean#L616-L640

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PullUUnitsCompatGeneric
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_GlobalFnsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsCommonField
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm

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

theorem GlobalTheory.ArcTransport.transport (hG : GlobalFnsSt) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X) (hW : WitData a P oP φ he w e)
    (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing (PowerSeries k)) F] [Algebra (FractionRing k) F] (uF : F)
    (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
    (hu : uF = algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ PowerSeries.X))
    (n : ℕ) (hn₀ : 0 < n) (hn : n ∣ l.M') :
    (∀ q₀ : QkPt a.D₀ F n, ∃ q : QkPt P.toPre F n, IsTransport a w e uF q₀ q) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n), IsTransport a w e uF q₀ q → q.g.b.left ≫ φ = q₀.g.b.left) ∧
    (∀ (q₀ : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀ q' →
      q = q') ∧
    (∀ (q₀ q₀' : QkPt a.D₀ F n) (q q' : QkPt P.toPre F n), IsTransport a w e uF q₀ q → IsTransport a w e uF q₀' q' →
      QkPt.Equiv a.D₀ F q₀ q₀' → QkPt.Equiv P.toPre F q q') ∧
    ∀ (q₀ : QkPt a.D₀ F n) (q : QkPt P.toPre F n) (t : a.D₀.X → F), IsTransport a w e uF q₀ q → q₀.y = 0 →
      (q₀.g.b = DegPre.zeroF a.D₀ F ∧ ∀ χ j, LB.Coh a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j →
        ⊤ ≤ LB.wchart a.D₀.P.L (DegPre.gtφ a.D₀ F q₀.g.b χ) j → valF (𝟙 (Sp F)) _ ((q₀.g.s χ).s j).val = t χ) →
      q.y = 0 ∧ q.g.b = DegPre.zeroF P.toPre F ∧ ∀ χ j, LB.Coh P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        ⊤ ≤ LB.wchart P.toPre.P.L (DegPre.gtφ P.toPre F q.g.b χ) j →
        valF (𝟙 (Sp F)) _ ((q.g.s χ).s j).val = t (e.symm χ) := by sorry
