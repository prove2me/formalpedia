-- Prove2me | Theorems.Thm_GlobalTheory_JetLinSub_jetPt_clm
-- name    : GlobalTheory.JetLinSub.jetPt_clm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T18:32:46.526142+00:00
-- url     : https://prove2.me/theorems/fe149820-203e-412e-8425-2dab06c8542a
-- title:
--   Jet Lin Sub: jet Pt clm
-- statement:
--   The Jet Lin Sub construction uses the jet Pt clm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L125-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/JetReadingLinearSubstitutionPoints.lean#L125-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_AnHolFamOfHolTo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_JetReadingLinearSubstitutionPoints
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.JetLinSub

theorem GlobalTheory.JetLinSub.jetPt_clm {Y : Scheme.{0}} {N N' : ℕ} (e : (Fin N → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (T : (Fin N' → ℂ) →L[ℂ] (Fin N → ℂ)) (e' : (Fin N' → ℂ) → (Sp ℂ ⟶ Y)) (hol' : IsHolFam e')
    (he : ∀ v, e' v = e (T v)) (m : ℕ) :
    spMap ((jetMap (anLin T) (anLin_mem T) : Jet ℂ (Fin 1 × Fin N) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin N') m) :
      Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ (Fin 1 × Fin N') m) ≫ jetPt e hol m = jetPt e' hol' m := by sorry
