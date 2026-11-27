-- Prove2me | Theorems.Thm_GlobalTheory_AnValJetGlob_appLE_spMap_jetPt
-- name    : GlobalTheory.AnValJetGlob.appLE_spMap_jetPt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:49.994379+00:00
-- url     : https://prove2.me/theorems/80b2a29b-30e6-4a74-b895-f8d8ad848e60
-- title:
--   An Val Jet Glob: app LE sp Map jet Pt
-- statement:
--   The An Val Jet Glob construction uses the app LE sp Map jet Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AppLESpMapJetPt.lean#L14-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/AppLESpMapJetPt.lean#L14-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolJetF
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_AppLESpMapJetPt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AnValJetGlob
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.AnValJetGlob.appLE_spMap_jetPt {N m : ℕ} {I : Type} {Z : Scheme.{0}} (q : (Fin N → ℂ) → (Sp ℂ ⟶ Z)) (hq : IsHolFam q)
    (χ : Jet ℂ (Fin 1 × Fin N) m →+* Jet ℂ I m) [IsLocalHom χ] (U : Z.Opens)
    (h : ⊤ ≤ (spMap χ ≫ jetPt q hq m) ⁻¹ᵁ U) :
    q 0 cpt ∈ U ∧ ∀ f : Γ(Z, U), (spMap χ ≫ jetPt q hq m).appLE U ⊤ h f =
      toΓ _ (χ (jetOf m fun v => valAt' (q v) U f)) := by sorry
