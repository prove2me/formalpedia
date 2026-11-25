-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_dataRigidSt_iff
-- name    : GlobalTheory.HostModel.dataRigidSt_iff
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:20:08.35774+00:00
-- url     : https://prove2.me/theorems/32562f15-4daf-4665-928e-909b0e2f5c06
-- title:
--   Host Model: data Rigid St iff
-- statement:
--   The Host Model construction uses the data Rigid St iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L36-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L36-L46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsPrimitiveRootArcRoot
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_ArcVarZpowInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsWitDataLevelAgree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HostModel
open ToricData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.HostModel.dataRigidSt_iff : DataRigidSt ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (c : Coeff l)
      (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
      (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) [Module (𝓞 E) P.toPre.X]
      (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ₁ φ₂ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
      (he₁ : eSec P.toPre.P.A ≫ φ₁ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
      (he₂ : eSec P.toPre.P.A ≫ φ₂ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
      (w₁ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₁)) (w₂ : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ₂))
      (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
      WitData a P oP φ₁ he₁ w₁ e₁ → WitData a P oP φ₂ he₂ w₂ e₂ → LevelAgree a P w₁ w₂ e₁ e₂ →
      φ₁ = φ₂ ∧ e₁ = e₂ ∧ HEq w₁ w₂ := by sorry
