-- Prove2me | Theorems.Thm_GroundTheory_Global_finite_setOf_mem_asIdeal
-- name    : GroundTheory.Global.finite_setOf_mem_asIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:18.094465+00:00
-- url     : https://prove2.me/theorems/7282880d-c571-4a3a-9b88-fee285948124
-- title:
--   Global: finite set Of mem as Ideal
-- statement:
--   The Global construction uses the finite set Of mem as Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L30-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L30-L33

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}

theorem GroundTheory.Global.finite_setOf_mem_asIdeal {b : 𝓞 L} (hb : b ≠ 0) :
    {v : HeightOneSpectrum (𝓞 L) | b ∈ v.asIdeal}.Finite := by sorry
