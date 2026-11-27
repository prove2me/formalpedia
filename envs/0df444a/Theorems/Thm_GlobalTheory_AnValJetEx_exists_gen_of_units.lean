-- Prove2me | Theorems.Thm_GlobalTheory_AnValJetEx_exists_gen_of_units
-- name    : GlobalTheory.AnValJetEx.exists_gen_of_units
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:29.493373+00:00
-- url     : https://prove2.me/theorems/166b8194-bbee-59a4-bf0e-1750f8c7d701
-- title:
--   An Val Jet Ex: exists gen of units
-- statement:
--   The An Val Jet Ex construction uses the exists gen of units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L52-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsGeneratorJetReading.lean#L52-L79

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

theorem GlobalTheory.AnValJetEx.exists_gen_of_units {X Y : Scheme.{0}} (L : LB X) (hY : ∀ p q : Y, p = q) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (u : K → L.ι → Γ(Y, ⊤)ˣ)
    (hu : ∀ k j j' (h : ⊤ ≤ φ k ⁻¹ᵁ (L.U j ⊓ L.U j')),
      (u k j).val = ((φ k).appLE _ ⊤ h).hom (L.g j j').val * (u k j').val) :
    ∃ τ : LB.Gen (LB.LinComb L φ ε), τ.IsGen ∧ ∀ (j : K → L.ι) (h : ⊤ ≤ LB.wchart L φ j),
      (Y.presheaf.map (homOfLE h).op).hom (τ.s j).val = (∏ k, u k (j k) ^ ε k).val := by sorry
