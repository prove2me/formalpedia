-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_UnivJets_ker_aug_eq
-- name    : GlobalTheory.PowGerm.UnivJets.ker_aug_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T14:14:36.894171+00:00
-- url     : https://prove2.me/theorems/dbcd41c3-820c-5287-9751-80a5139d22d6
-- title:
--   Univ Jets: ker aug eq
-- statement:
--   The Univ Jets construction uses the ker aug eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L32-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L32-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetAug_zR
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_jetLift_zR
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
variable {V : Type} [CommRing V]
open Chart (JetR zR jetAug_zR jet_ext jetLift jetLift_zR ker_jetAug_pow zR_mem_ker)

theorem GlobalTheory.PowGerm.UnivJets.ker_aug_eq (κ : Type) (m : ℕ) : RingHom.ker (Chart.jetAug V κ m) =
    (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ V))).map (Ideal.Quotient.mk _) := by sorry
