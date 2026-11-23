-- Prove2me | Theorems.Thm_GlobalTheory_T_isAffineCombination_independent_of_chart
-- name    : GlobalTheory.T.isAffineCombination_independent_of_chart
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:12.94967+00:00
-- url     : https://prove2.me/theorems/be1f8b47-479a-4a1b-a867-fb502d17f410
-- title:
--   T: is Affine Combination independent of chart
-- statement:
--   The T construction uses the is Affine Combination independent of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChartStatement.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationIndependentOfChartStatement.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChartStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isAffineCombination_independent_of_chart : ∀ (Y : Scheme.{0}) (V V' : Y.Opens), IsAffineOpen V → IsAffineOpen V' →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u c : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S),
    (∀ i, spMap q ≫ w i = spMap q ≫ u) → GlobalTheory.SecGlue.IsCombIn V u c w a → u ⁻¹ᵁ V' = ⊤ →
    GlobalTheory.SecGlue.IsCombIn V' u c w a := by sorry
