-- Prove2me | Theorems.Thm_GlobalTheory_ProdFinCastLE_prod_fin_eq_prod_castLE
-- name    : GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:56:26.439534+00:00
-- url     : https://prove2.me/theorems/b7db4245-476c-424b-b0ee-4871e94d2974
-- title:
--   Prod Fin Cast LE: prod fin eq prod cast LE
-- statement:
--   The Prod Fin Cast LE construction uses the prod fin eq prod cast LE property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ProdFinEqProdCastLE.lean#L5-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/ProdFinEqProdCastLE.lean#L5-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ProdFinEqProdCastLE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ProdFinCastLE

theorem GlobalTheory.ProdFinCastLE.prod_fin_eq_prod_castLE {a b : ℕ} {M : Type} [CommMonoid M] (h : a ≤ b) (f : Fin b → M)
    (hf : ∀ r : Fin b, a ≤ (r : ℕ) → f r = 1) :
    ∏ r : Fin b, f r = ∏ r : Fin a, f (Fin.castLE h r) := by sorry
