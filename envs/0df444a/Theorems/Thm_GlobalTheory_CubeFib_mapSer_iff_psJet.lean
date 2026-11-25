-- Prove2me | Theorems.Thm_GlobalTheory_CubeFib_mapSer_iff_psJet
-- name    : GlobalTheory.CubeFib.mapSer_iff_psJet
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:04:39.058804+00:00
-- url     : https://prove2.me/theorems/ee0c534e-25a5-4706-85ef-0898323b08a6
-- title:
--   Cube Fib: map Ser iff ps Jet
-- statement:
--   The Cube Fib construction uses the map Ser iff ps Jet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L164-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L164-L176

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_StChartFH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubicalPullBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_IsFormalGroupLawOfChartOfJetChart
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TeichmullerDepth_PsJetEqToJetOfNonempty
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
open GlobalTheory GlobalTheory.CubeFib
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators
attribute [local instance] Over.cartesianMonoidalCategory
variable {k : Type} [CommRing k] {d g : ℕ}

theorem GlobalTheory.CubeFib.mapSer_iff_psJet {G B : Over (Sp k)} (q : G ⟶ B) (x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G)
    (y : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin g) m) ⟶ B) (ψ : Fin g → PS k 1 d) :
    MapSer q x y ψ ↔ (∀ j, MvPowerSeries.constantCoeff (ψ j) = 0) ∧
      ∀ m : ℕ, ∃ a : JetR k (Fin 1 × Fin g) m →ₐ[k] JetR k (Fin 1 × Fin d) m,
        (∀ j, a (zR m ((0 : Fin 1), j)) = psJet m (ψ j)) ∧ x m ≫ q = algOverHom a ≫ y m := by sorry
