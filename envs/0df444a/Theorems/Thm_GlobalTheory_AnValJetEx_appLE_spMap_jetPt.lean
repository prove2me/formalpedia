-- Prove2me | Theorems.Thm_GlobalTheory_AnValJetEx_appLE_spMap_jetPt
-- name    : GlobalTheory.AnValJetEx.appLE_spMap_jetPt
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T04:52:56.174806+00:00
-- url     : https://prove2.me/theorems/aacd5e87-782a-405b-a0c0-9c8ac95ef813
-- title:
--   An Val Jet Ex: app LE sp Map jet Pt
-- statement:
--   The An Val Jet Ex construction uses the app LE sp Map jet Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L126-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L126-L137

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsGeneratorJetReading
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
open GlobalTheory GlobalTheory.AnValJetEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
open scoped ContDiff
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValJetEx.appLE_spMap_jetPt {d : ℕ} {Y : Scheme.{0}} (e : (Fin d → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e) (m : ℕ)
    {R : Type} [CommRing R] (r : Jet ℂ (Fin 1 × Fin d) m →+* R) (U : Y.Opens) (hU : e 0 cpt ∈ U)
    (h : ⊤ ≤ (spMap r ≫ jetPt e hol m) ⁻¹ᵁ U) (a : Γ(Y, U)) :
    ((spMap r ≫ jetPt e hol m).appLE U ⊤ h).hom a = toΓ R (r (jetOf m fun z => valAt' (e z) U a)) := by sorry
