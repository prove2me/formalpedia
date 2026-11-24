-- Prove2me | Theorems.Thm_GlobalTheory_derivation_inner_of_separability_element
-- name    : GlobalTheory.derivation_inner_of_separability_element
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:08.478421+00:00
-- url     : https://prove2.me/theorems/c1e2826c-5113-4646-9704-394355eb36e1
-- title:
--   Global Theory: derivation inner of separability element
-- statement:
--   The Global Theory construction uses the derivation inner of separability element property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DerivationInnerOfSeparabilityElement.lean#L10-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/DerivationInnerOfSeparabilityElement.lean#L10-L50

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_DerivationInnerOfSeparabilityElement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory

theorem GlobalTheory.derivation_inner_of_separability_element (O : Type) [CommRing O] (N : ℕ)
    (e : TensorProduct ℤ O O) (hN : 0 < N) (he : Algebra.TensorProduct.lmul' ℤ e = (N : O))
    (hc : ∀ c : O, (TensorProduct.tmul ℤ c (1 : O) - TensorProduct.tmul ℤ (1 : O) c) * e = 0)
    (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V)
    (hlr : ∀ a b, Commute (l a) (r b)) (δ : O →+ V)
    (hδ : ∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) :
    ∃ v : V, ∀ a, δ a = l a v - r a v := by sorry
