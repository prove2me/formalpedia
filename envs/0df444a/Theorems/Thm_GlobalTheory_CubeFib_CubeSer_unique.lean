-- Prove2me | Theorems.Thm_GlobalTheory_CubeFib_CubeSer_unique
-- name    : GlobalTheory.CubeFib.CubeSer.unique
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:38.233515+00:00
-- url     : https://prove2.me/theorems/ba9e6695-a3f7-4b83-8548-ad240cac62e8
-- title:
--   Cube Ser: unique
-- statement:
--   The Cube Ser construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L122-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/TeichmullerDepth/PsJetEqToJetOfNonempty.lean#L122-L129

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

theorem GlobalTheory.CubeFib.CubeSer.unique {G : Over (Sp k)} [GrpObj G] [IsCommMonObj G] {L : RigLB G} {c : CubicalStr G L}
    {x : ∀ m : ℕ, algOver k (JetR k (Fin 1 × Fin d) m) ⟶ G} {i : L.L.ι} {Φ Φ' : PS k 3 d}
    (h : CubeSer c x i Φ) (h' : CubeSer c x i Φ') : Φ = Φ' := by sorry
