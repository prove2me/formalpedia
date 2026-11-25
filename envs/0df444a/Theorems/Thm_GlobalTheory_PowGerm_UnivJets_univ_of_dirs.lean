-- Prove2me | Theorems.Thm_GlobalTheory_PowGerm_UnivJets_univ_of_dirs
-- name    : GlobalTheory.PowGerm.UnivJets.univ_of_dirs
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T13:56:29.532534+00:00
-- url     : https://prove2.me/theorems/03033b0b-dfc9-5542-8ba4-210cf64c85a2
-- title:
--   Univ Jets: univ of dirs
-- statement:
--   The Univ Jets construction uses the univ of dirs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L157-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UniversalStatement.lean#L157-L235

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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

theorem GlobalTheory.PowGerm.UnivJets.univ_of_dirs {d : ℕ} {κ : Type} [Fintype κ] (β : Fin d ≃ κ)
    {x : ∀ m, Chart.sp (R₀ := V) (JetR V (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (z : ∀ m, Chart.sp (R₀ := V) (JetR V κ m) ⟶ G)
    (htr : ∀ m, Chart.spMap (jetTruncR V κ m) ≫ z (m + 1) = z m)
    (haug : ∀ m, Chart.spMap (Chart.jetAug V κ m) ≫ z m = 1)
    (t : Fin d → (JetR V κ 1 →ₐ[V] DualNumber V))
    (ht : ∀ j k, t j (zR 1 (β k)) = if k = j then DualNumber.eps else 0)
    (hdir : ∀ j, Chart.spMap (t j) ≫ z 1 = Chart.spMap (dualLift (Pi.single j 1)) ≫ x 1)
    (A : Type) [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hA : RingHom.ker aug ^ (m + 1) = ⊥)
    (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap aug ≫ y = 1) :
    ∃! ψ : JetR V κ m →ₐ[V] A, aug.comp ψ = Chart.jetAug V κ m ∧ y = Chart.spMap ψ ≫ z m := by sorry
