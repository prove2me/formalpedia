-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_localizationAt_iff
-- name    : GroundTheory.Global.mem_localizationAt_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:42:22.122682+00:00
-- url     : https://prove2.me/theorems/7fdce1a0-8325-4a1e-8798-914c3c2639b5
-- title:
--   Global: mem localization At iff
-- statement:
--   The Global construction uses the mem localization At iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L22-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L22-L28

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

theorem GroundTheory.Global.mem_localizationAt_iff {v : HeightOneSpectrum (𝓞 L)} {x : L} :
    x ∈ localizationAt L v ↔ ∃ a s : 𝓞 L, s ∉ v.asIdeal ∧
      x = algebraMap (𝓞 L) L a * (algebraMap (𝓞 L) L s)⁻¹ := by sorry
