-- Prove2me | Theorems.Thm_GlobalTheory_Published_ComplexMultiplicationJSt_map_j
-- name    : GlobalTheory.Published.ComplexMultiplicationJSt.map_j
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:05.83375+00:00
-- url     : https://prove2.me/theorems/0a295b69-1785-44b5-a244-a402512242ea
-- title:
--   Complex Multiplication JSt: map j
-- statement:
--   The Complex Multiplication JSt construction uses the map j property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L114-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/PublishedFoundations/ComplexMultiplicationJPremises.lean#L114-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]

theorem GlobalTheory.Published.ComplexMultiplicationJSt.map_j (h : ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : IsHilbertClassField H)
    {art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hart : IsArtinMap art)
    {𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L L' : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (hL' : IsIdealLattice (𝔟⁻¹ * 𝔞) L') (ρ : ℂ →+* ℂ)
    (hρ : ∀ x : H, ρ x = art (ClassGroup.mk K 𝔟) x) :
    ρ (latticeCurve L).j = (latticeCurve L').j := by sorry
