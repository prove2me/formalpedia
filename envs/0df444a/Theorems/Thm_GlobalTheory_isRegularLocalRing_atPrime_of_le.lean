-- Prove2me | Theorems.Thm_GlobalTheory_isRegularLocalRing_atPrime_of_le
-- name    : GlobalTheory.isRegularLocalRing_atPrime_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:16:35.278557+00:00
-- url     : https://prove2.me/theorems/541c7807-8d5c-4b3f-b35f-cfe3e71a606b
-- title:
--   Global Theory: is Regular Local Ring at Prime of le
-- statement:
--   The Global Theory construction uses the is Regular Local Ring at Prime of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagata.lean#L9-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsOpenRegularLocusOfNagata.lean#L9-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularNearOfRegularQuotientPrimeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsOpenRegularLocusOfNagata
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing TensorProduct
open GlobalTheory

theorem GlobalTheory.isRegularLocalRing_atPrime_of_le {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by sorry
