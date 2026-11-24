-- Prove2me | Theorems.Thm_GroundTheory_Global_isUnit_of_mem_of_inv_mem
-- name    : GroundTheory.Global.isUnit_of_mem_of_inv_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:28.715034+00:00
-- url     : https://prove2.me/theorems/48f20ee7-4fb8-4e1c-b126-838b14645a0b
-- title:
--   Global: is Unit of mem of inv mem
-- statement:
--   The Global construction uses the is Unit of mem of inv mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L45-L47

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
omit [NumberField L]

theorem GroundTheory.Global.isUnit_of_mem_of_inv_mem {R : Type*} [CommRing R] [Algebra R L] {S : Subalgebra R L}
    {x : L} (hx : x ≠ 0) (h : x ∈ S) (h' : x⁻¹ ∈ S) : IsUnit (⟨x, h⟩ : S) := by sorry
