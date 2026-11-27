-- Prove2me | Theorems.Thm_GlobalTheory_OrbitMass_card_stab
-- name    : GlobalTheory.OrbitMass.card_stab
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:35.629035+00:00
-- url     : https://prove2.me/theorems/804038a7-4488-443d-99ad-d2d2827c76ac
-- title:
--   Orbit Mass: card stab
-- statement:
--   The Orbit Mass construction uses the card stab property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitMassFormulaFiniteIndexSubgroup.lean#L55-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/OrbitMassFormulaFiniteIndexSubgroup.lean#L55-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OrbitMassFormulaFiniteIndexSubgroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MulAction
open GlobalTheory GlobalTheory.OrbitMass
variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

theorem GlobalTheory.OrbitMass.card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by sorry
