-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_UnivJets_toFirst_comp
-- name    : GlobalTheory.PowGerm.UnivJets.toFirst_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T14:20:59.348475+00:00
-- url     : https://prove2.me/theorems/7d1aa200-ffde-57a0-89f5-128ce72e97be
-- title:
--   Univ Jets: to First comp
-- statement:
--   The Univ Jets construction uses the to First comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L148-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L148-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jet_ext
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_ker_jetAug_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_zR_mem_ker

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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.PowGerm GlobalTheory.PowGerm.UnivJets
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
open Chart (JetR zR jetAug_zR jet_ext ker_jetAug_pow zR_mem_ker jetTruncR dualLift dualLift_zR fstD kerD_sq)
omit [GrpObj G]

theorem GlobalTheory.PowGerm.UnivJets.toFirst_comp {κ : Type} (z : ∀ m, Chart.sp (R₀ := V) (JetR V κ m) ⟶ G)
    (htr : ∀ m, Chart.spMap (jetTruncR V κ m) ≫ z (m + 1) = z m) (m : ℕ) :
    Chart.spMap (toFirst κ m) ≫ z (m + 1) = z 1 := by sorry
