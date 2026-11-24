-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_maximalIdeal_pow_iff
-- name    : GroundTheory.Global.mem_maximalIdeal_pow_iff
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:27.376813+00:00
-- url     : https://prove2.me/theorems/ba2f56b1-8047-4ccd-8a56-ac0e443efeab
-- title:
--   Global: mem maximal Ideal pow iff
-- statement:
--   The Global construction uses the mem maximal Ideal pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L180-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CompletionAtPlace/Integers.lean#L180-L187

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace
import Definitions.Def_GroundTheory_GlobalFields_CompletionAtPlace_Integers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField ValuativeRel
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {F : Type*} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))

theorem GroundTheory.Global.mem_maximalIdeal_pow_iff (y : 𝒪[u.adicCompletion F]) (n : ℕ) :
    y ∈ 𝓂[u.adicCompletion F] ^ n ↔ Valued.v (y : u.adicCompletion F) ≤ WithZero.exp (-(n : ℤ)) := by sorry
