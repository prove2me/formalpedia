-- Prove2me | Theorems.Thm_GlobalTheory_ThetaPtMove_isValueAt_of_sv
-- name    : GlobalTheory.ThetaPtMove.isValueAt_of_sv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T14:30:04.871847+00:00
-- url     : https://prove2.me/theorems/dcccd95a-12c9-4421-a597-af8e3e14d876
-- title:
--   Theta Pt Move: is Value At of sv
-- statement:
--   The Theta Pt Move construction uses the is Value At of sv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L44-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaFamilyOrigin/IsThetaPtOverMove.lean#L44-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsIffCommIsOfAndLiftSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_WeilIsGrpPullbackOfCommute
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_LinearIndependentOfIsExtension
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsThetaPtOverMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ThetaPtMove
open GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {n : ℤ} {T : Over S}
  {s : LB.Sec (LPow A L n T)} {x : T ⟶ A}
  {ρ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => n))} {c : Γ(T.left, ⊤)}

theorem GlobalTheory.ThetaPtMove.isValueAt_of_sv (hL : L.IsLB) (h : ∀ y J, Good L y J →
    VVRank.sv A s (𝟙 _ ≫ (ptSecT A x).left) y J = gs (𝟙 _) y ⊤ c * (val ρ (𝟙 _) y J).val) :
    IsValueAt A L n s x ρ c := by sorry
