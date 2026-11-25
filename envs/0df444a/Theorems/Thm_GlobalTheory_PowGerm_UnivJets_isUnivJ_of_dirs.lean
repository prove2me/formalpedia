-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_UnivJets_isUnivJ_of_dirs
-- name    : GlobalTheory.PowGerm.UnivJets.isUnivJ_of_dirs
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:56:18.026165+00:00
-- url     : https://prove2.me/theorems/6233faf2-10e4-590a-8359-41b2c98526c8
-- title:
--   Univ Jets: is Univ J of dirs
-- statement:
--   The Univ Jets construction uses the is Univ J of dirs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L258-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L258-L285

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_SaturationChartsHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UniversalStatement
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
variable {V : Type} [CommRing V] {G : Over (Sp V)}

theorem GlobalTheory.PowGerm.UnivJets.isUnivJ_of_dirs [GrpObj G] {d : ℕ}
    {x : ∀ m, Chart.sp (R₀ := V) (Chart.JetR V (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (z : JetPts G (Fin 1 × Fin d))
    (htr : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ z (m + 1) = z m)
    (haug : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ z m = 1)
    (hdir : ∀ j, idAt _ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ z 1 =
        Chart.spMap (Chart.dualLift (Pi.single j 1)) ≫ x 1) :
    IsUnivJ G (Fin 1 × Fin d) z := by sorry
