-- Prove2me | Theorems.Thm_GlobalTheory_WeilMul_CommV_mul
-- name    : GlobalTheory.WeilMul.CommV.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:09:19.238933+00:00
-- url     : https://prove2.me/theorems/eb6a9b2d-4f85-47dd-b9b5-3ebee64a3797
-- title:
--   Comm V: mul
-- statement:
--   The Comm V construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L172-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsCommVOfLe.lean#L172-L183

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsCommVOfLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WeilMul
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {k : ℤ}

theorem GlobalTheory.WeilMul.CommV.mul [IsCommMonObj A] (hL : L.IsLB) {T T₀ : Over S}
    {θx θx' θy : ThetaGrp A L k T} {g : T ⟶ T₀} {c c' : Γ(T₀.left, ⊤)ˣ} (h : CommV θx θy g c)
    (h' : CommV θx' θy g c') : ∃ θ : ThetaGrp A L k T, θ.pt = θx.pt * θx'.pt ∧ CommV θ θy g (c * c') := by sorry
