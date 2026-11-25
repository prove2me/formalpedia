-- Prove2me | Theorems.Thm_GlobalTheory_LocalLift_exists_local_lift
-- name    : GlobalTheory.LocalLift.exists_local_lift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:42:29.034518+00:00
-- url     : https://prove2.me/theorems/a7d26356-a329-5755-80bf-752ea5b3e534
-- title:
--   Local Lift: exists local lift
-- statement:
--   The Local Lift construction uses the exists local lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HolDifferentiableAt.lean#L191-L478
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/HolDifferentiableAt.lean#L191-L478

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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open Filter Topology
variable {Y : Scheme.{0}}

theorem GlobalTheory.LocalLift.exists_local_lift : ∀ (Y : Scheme.{0}) (s : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ)
    (g g' : ℕ) (e : (Fin g → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)) (e' : (Fin g' → ℂ) → (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp ℂ ⟶ Y)),
    Smooth s → (∀ z, e z ≫ s = 𝟙 _) → (∀ z, e' z ≫ s = 𝟙 _) → _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e →
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsHolTo Set.univ e' →
    ((∀ w, ∃! v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) ∧
      ∀ v : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber ℂ) ⟶ Y, v ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap ℂ (DualNumber ℂ)) →
        _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e' 0 → ∃! w, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsDerivAt0 e' w v) →
    e 0 = e' 0 → ∃ k₀ : (Fin g → ℂ) → (Fin g' → ℂ), k₀ 0 = 0 ∧ AnalyticAt ℂ k₀ 0 ∧
      ∀ᶠ z in nhds (0 : Fin g → ℂ), e' (k₀ z) = e z := by sorry
