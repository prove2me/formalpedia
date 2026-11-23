-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_preimage_eq_of_comp_eq_of_sqZero
-- name    : GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:26.831064+00:00
-- url     : https://prove2.me/theorems/fef1076f-3e44-4ba4-a17e-4a32913f0f64
-- title:
--   Sec Glue: preimage eq of comp eq of sq Zero
-- statement:
--   The Sec Glue construction uses the preimage eq of comp eq of sq Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageEqOfSquareZeroThickening.lean#L6-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PreimageEqOfSquareZeroThickening.lean#L6-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.preimage_eq_of_comp_eq_of_sqZero : ∀ (S T : Type) [CommRing S] [CommRing T] (q : S →+* T),
    Function.Surjective q → RingHom.ker q ^ 2 = ⊥ →
    ∀ (Y : Scheme.{0}) (u w : Sp S ⟶ Y), spMap q ≫ u = spMap q ≫ w → ∀ V : Y.Opens,
      u ⁻¹ᵁ V = w ⁻¹ᵁ V := by sorry
