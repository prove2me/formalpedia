-- Prove2me | Theorems.Thm_GlobalTheory_RelationPowers_rel_prod_pow
-- name    : GlobalTheory.RelationPowers.rel_prod_pow
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:21:01.496867+00:00
-- url     : https://prove2.me/theorems/e7a4bd60-fb4a-4462-9eef-edb4120d4eaf
-- title:
--   Relation Powers: rel prod pow
-- statement:
--   The Relation Powers construction uses the rel prod pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RelProdPow.lean#L14-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/RelProdPow.lean#L14-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RelProdPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.RelationPowers

theorem GlobalTheory.RelationPowers.rel_prod_pow {G U : Type} [Monoid G] [CommMonoid U] (R : G → U → Prop) (h1 : R 1 1)
    (hmul : ∀ (x x' : G) (c c' : U), R x c → R x' c' → R (x * x') (c * c'))
    (n : ℕ) (y : Fin n → G) (c : Fin n → U) (a : Fin n → ℕ) (h : ∀ i, R (y i) (c i)) :
    R (List.prod (List.ofFn fun i : Fin n => y i ^ a i)) (∏ i : Fin n, c i ^ a i) := by sorry
