-- Prove2me | Theorems.Thm_GlobalTheory_HostModel_eq_of_genRel
-- name    : GlobalTheory.HostModel.eq_of_genRel
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T18:26:22.475257+00:00
-- url     : https://prove2.me/theorems/4b278698-a95c-5dea-91cf-af3d556ababb
-- title:
--   Host Model: eq of gen Rel
-- statement:
--   The Host Model construction uses the eq of gen Rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L123-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsWitDataLevelAgree.lean#L123-L138

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
variable (F : Type) [Field F] [Algebra (FractionRing (PowerSeries k)) F]
variable [Algebra (FractionRing k) F]
  (hF : ∀ x, algebraMap (FractionRing k) F (algebraMap k _ x) =
    algebraMap (FractionRing (PowerSeries k)) F (algebraMap (PowerSeries k) _ (PowerSeries.C x)))
include hF

theorem GlobalTheory.HostModel.eq_of_genRel {n : ℕ} (e : 𝓞 E ≃ₗ[𝓞 E] 𝓞 E) (x : 𝓞 E → F) (q₀ : QkPt (arcIn c k bF).D₀ F n)
    (q₁ q₂ : QkPt (witP c k bF).toPre F n) (hy : q₁.y = q₂.y)
    (h₁ : ∀ z, GenRel (witIso c k bF) (q₁.g.s (e z)) (q₀.g.s z) (x z))
    (h₂ : ∀ z, GenRel (witIso c k bF) (q₂.g.s (e z)) (q₀.g.s z) (x z)) : q₁ = q₂ := by sorry
