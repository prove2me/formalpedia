-- Prove2me | Theorems.Thm_GlobalTheory_AnValGenCorr_corr_val
-- name    : GlobalTheory.AnValGenCorr.corr_val
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T04:37:38.357844+00:00
-- url     : https://prove2.me/theorems/cf6c17b6-6665-5cce-91f9-fd30f670998a
-- title:
--   An Val Gen Corr: corr val
-- statement:
--   The An Val Gen Corr construction uses the corr val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingCorrMulInv.lean#L31-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/GeneratorReadingCorrMulInv.lean#L31-L45

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ThConst
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_GeneratorReadingCorrMulInv
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
open GlobalTheory GlobalTheory.AnValGenCorr
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.AnValGenCorr.corr_val {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')) (hc : LB.Gen.Corr L φ ε φ' ε' t t')
    (J : (Y ⟶ X) → L.ι) (p : Sp ℂ ⟶ Y) (hJ : ∀ ψ, ⊤ ≤ (p ≫ ψ) ⁻¹ᵁ L.U (J ψ)) :
    valAt' p (LB.wchart L φ fun k => J (φ k)) (t.s fun k => J (φ k)).val =
      valAt' p (LB.wchart L φ' fun k => J (φ' k)) (t'.s fun k => J (φ' k)).val := by sorry
