-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_CombEx_exists_comb
-- name    : GlobalTheory.SecGlue.CombEx.exists_comb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:53:13.122853+00:00
-- url     : https://prove2.me/theorems/7189bf84-8f1e-40b8-bf5e-4a2920243cdd
-- title:
--   Comb Ex: exists comb
-- statement:
--   The Comb Ex construction uses the exists comb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L111-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsAffineCombinationSquareZeroLiftsChart.lean#L111-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.CombEx

theorem GlobalTheory.SecGlue.CombEx.exists_comb : ∀ (Y : Scheme.{0}) (V : Y.Opens), IsAffineOpen V →
    ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T), Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (ι : Type) [Fintype ι] (u : Sp S ⟶ Y) (w : ι → (Sp S ⟶ Y)) (a : ι → S), u ⁻¹ᵁ V = ⊤ →
    (∀ i, spMap q ≫ w i = spMap q ≫ u) →
    ∃ c : Sp S ⟶ Y, GlobalTheory.SecGlue.IsCombIn V u c w a ∧ spMap q ≫ c = spMap q ≫ u ∧
      ∀ (R' : Type) [CommRing R'] (p : Y ⟶ Sp R'), (∀ i, w i ≫ p = u ≫ p) → c ≫ p = u ≫ p := by sorry
