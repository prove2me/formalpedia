-- Prove2me | Theorems.Thm_GlobalTheory_LocalLift_exists_tangent
-- name    : GlobalTheory.LocalLift.exists_tangent
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:52:52.516703+00:00
-- url     : https://prove2.me/theorems/3a32882f-60bc-58bd-ab85-31fe671144c0
-- title:
--   Local Lift: exists tangent
-- statement:
--   The Local Lift construction uses the exists tangent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HolDifferentiableAt.lean#L120-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HolDifferentiableAt.lean#L120-L154

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_FlagBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_EigLatBasis
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_CubicalExtendsSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_HolDifferentiableAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Filter Topology GlobalTheory.TangentOrigin
noncomputable section
open GlobalTheory GlobalTheory.LocalLift
variable {Y : Scheme.{0}}

theorem GlobalTheory.LocalLift.exists_tangent {n : ℕ} (s : Y ⟶ Sp ℂ) {W : Set (Fin n → ℂ)} (hW : 0 ∈ W) {p : (Fin n → ℂ) → (Sp ℂ ⟶ Y)}
    (hp : IsHolTo W p) (hps : ∀ w, p w ≫ s = 𝟙 _) {U : Y.Opens} (hU : IsAffineOpen U) (h0 : ⊤ ≤ p 0 ⁻¹ᵁ U)
    (u : Fin n → ℂ) :
    ∃ (v : Sp (DualNumber ℂ) ⟶ Y) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ s = spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      spMap fstC ≫ v = p 0 ∧ ∀ f, (evalPt v U h f).snd = fderiv ℂ (fun z => valAt' (p z) U f) 0 u := by sorry
