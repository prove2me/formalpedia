-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_exists_witData
-- name    : GlobalTheory.HostModel.exists_witData
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:25:45.299373+00:00
-- url     : https://prove2.me/theorems/2f5be5ed-c63a-5331-a328-d13effd31144
-- title:
--   Host Model: exists wit Data
-- statement:
--   The Host Model construction uses the exists wit Data property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L93-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L93-L102

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
variable {l : Level H} (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k)

theorem GlobalTheory.HostModel.exists_witData : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (D : Datum H)
    (l : Level H) (c : Coeff l) (k : Type) (_ : Field k) (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (P : DegData (PowerSeries k) (Ideal.span {PowerSeries.X})) (_ : Module (𝓞 E) P.toPre.X)
    (oP : letI := H.starRing; P.toPre.OAct (𝓞 E)) (φ : P.toPre.P.A.left ⟶ a.D₀.P.A.left)
    (he : eSec P.toPre.P.A ≫ φ = spMap (PowerSeries.C (R := k)) ≫ eSec a.D₀.P.A)
    (w : LB.Iso P.toPre.P.L (a.D₀.P.L.pull φ)) (e₁ e₂ : a.D₀.X ≃ₗ[𝓞 E] P.toPre.X),
    e₁ ≠ e₂ ∧ WitData a P oP φ he w e₁ ∧ WitData a P oP φ he w e₂ := by sorry
