-- Prove2me | Theorems.Thm_GlobalTheory_thetaGrp_acts_linearly
-- name    : GlobalTheory.thetaGrp_acts_linearly
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:26.172794+00:00
-- url     : https://prove2.me/theorems/04afed3b-9b70-4c2c-9913-eaf04c63a5d8
-- title:
--   Global Theory: theta Grp acts linearly
-- statement:
--   The Global Theory construction uses the theta Grp acts linearly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ThetaGrpActsLinearly.lean#L217-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ThetaGrpActsLinearly.lean#L217-L238

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_WeilIsAlternatingSkewNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ThetaGrpActsLinearly
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open ThetaAct CommPairing

theorem GlobalTheory.thetaGrp_acts_linearly : GlobalFnsSt → ∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v) := by sorry
