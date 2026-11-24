-- Prove2me | Theorems.Thm_GlobalTheory_RegularAscent_exists_regular_near_of_regular_quotient
-- name    : GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T19:19:47.811832+00:00
-- url     : https://prove2.me/theorems/43b58c2e-8233-4b20-99f1-d910d5b78e39
-- title:
--   Regular Ascent: exists regular near of regular quotient
-- statement:
--   The Regular Ascent construction uses the exists regular near of regular quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularNearOfRegularQuotientPrime.lean#L78-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularNearOfRegularQuotientPrime.lean#L78-L178

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsRegularLocalRingOfRegularQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMinimalLocalGeneratorsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory GlobalTheory.RegularAscent
open IsLocalRing TensorProduct

theorem GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient (B : Type) [CommRing B]
    [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
      IsRegularLocalRing
        (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by sorry
