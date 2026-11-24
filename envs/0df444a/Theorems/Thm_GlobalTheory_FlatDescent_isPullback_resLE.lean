-- Prove2me | Theorems.Thm_GlobalTheory_FlatDescent_isPullback_resLE
-- name    : GlobalTheory.FlatDescent.isPullback_resLE
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:35.279263+00:00
-- url     : https://prove2.me/theorems/a9e0963d-3409-4f68-8f42-83e967f6e3dd
-- title:
--   Flat Descent: is Pullback res LE
-- statement:
--   The Flat Descent construction uses the is Pullback res LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L80-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsAppTopEqOfEffectiveEpi.lean#L80-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsAppTopEqOfEffectiveEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry Opposite
open GlobalTheory
open GlobalTheory.FlatDescent
universe u
variable {X Y Z : Scheme.{u}}

theorem GlobalTheory.FlatDescent.isPullback_resLE {p : Y ⟶ X} {f g : Z ⟶ Y} (h : IsPullback f g p p) (U : X.Opens)
    (W : Z.Opens) (hW : W = f ⁻¹ᵁ p ⁻¹ᵁ U) (hf : W ≤ f ⁻¹ᵁ p ⁻¹ᵁ U) (hg : W ≤ g ⁻¹ᵁ p ⁻¹ᵁ U) :
    IsPullback (f.resLE _ W hf) (g.resLE _ W hg) (p ∣_ U) (p ∣_ U) := by sorry
