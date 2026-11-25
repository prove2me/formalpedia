-- Prove2me | Theorems.Thm_GlobalTheory_NsmulIntegersMembership_valued_absNorm_lt_one
-- name    : GlobalTheory.NsmulIntegersMembership.valued_absNorm_lt_one
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:15:04.270852+00:00
-- url     : https://prove2.me/theorems/cbdf6348-ad7f-4973-a6de-482d73f98f16
-- title:
--   Nsmul Integers Membership: valued abs Norm lt one
-- statement:
--   The Nsmul Integers Membership construction uses the valued abs Norm lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNsmulIntegersMem.lean#L8-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNsmulIntegersMem.lean#L8-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNsmulIntegersMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.NsmulIntegersMembership

theorem GlobalTheory.NsmulIntegersMembership.valued_absNorm_lt_one (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) :
    Valued.v ((Ideal.absNorm v.asIdeal : ℕ) : v.adicCompletion F) < 1 := by sorry
