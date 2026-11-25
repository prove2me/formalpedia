-- Prove2me | Theorems.Thm_GlobalTheory_LinkSec_change_index
-- name    : GlobalTheory.LinkSec.change_index
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T01:02:24.484003+00:00
-- url     : https://prove2.me/theorems/e351815a-09b6-45a9-b6c7-4d9be12f21a5
-- title:
--   Link Sec: change index
-- statement:
--   The Link Sec construction uses the change index property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GsSpMapGermAt.lean#L49-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/GsSpMapGermAt.lean#L49-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DivCalc
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_FBIdJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_IsLawOfOfMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ValSerGermFnVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniqueNormPrim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_GsSpMapGermAt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LinkSec

theorem GlobalTheory.LinkSec.change_index {S : Scheme.{0}} {G T T' : Over S} [GrpObj G] [IsCommMonObj G] {L : LB G.left} (w : G ⟶ G)
    (x : T ⟶ G) (s : T ⟶ T') (x₀ x₁ : T' ⟶ G) (h₀ : s ≫ x₀ = x) (h₁ : s ≫ x₁ = x ≫ w)
    (e : LB.Gen (LB.LinComb L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (cε 2)))
    (he : e.IsGen) (ρ : LB.Gen (LB.LinComb L (JetSer.primφ w) JetSer.primε)) (hρ : ρ.IsGen) (q : ℕ) (σ : H0 L q)
    (j : L.ι) (y : T.left) (hj : x.left y ∈ LB.wchart L (JetSer.primφ w) (fun _ => j)) (J) (hJ : Good L y J) :
    s.left y ∈ LB.wchart L (fun I : ULift.{0} (Finset (Fin 2)) => (psum G ![x₀, x₁] I.down).left) (fun _ => j) ∧
    ∃ c : (T.left.presheaf.stalk y)ˣ,
      sval σ x.left y J = (c ^ q).val * gs x.left y _ (σ.f fun _ => j) ∧
      val ρ x.left y J * val e s.left y J =
        c * (gm x.left y _ (ρ.s fun _ => j) * gm s.left y _ (e.s fun _ => j)) := by sorry
