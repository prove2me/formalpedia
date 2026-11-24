-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_isCombIn_of_chart
-- name    : GlobalTheory.SecGlue.isCombIn_of_chart
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:49:26.343877+00:00
-- url     : https://prove2.me/theorems/4e7b78ce-fb2a-4cd1-8aaa-29e1a4f2d19b
-- title:
--   Sec Glue: is Comb In of chart
-- statement:
--   The Sec Glue construction uses the is Comb In of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L142-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChart.lean#L142-L210

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SecGlue
open GlobalTheory GlobalTheory.SecGlue
open ChartIndep

theorem GlobalTheory.SecGlue.isCombIn_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by sorry
