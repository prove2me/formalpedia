-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_finite_abelian_mem
-- name    : GroundTheory.LocalField.exists_finite_abelian_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:40.068682+00:00
-- url     : https://prove2.me/theorems/7a0992cc-af03-4995-9910-065195495053
-- title:
--   Local Field: exists finite abelian mem
-- statement:
--   The Local Field construction uses the exists finite abelian mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L116-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalAbelianExtension.lean#L116-L153

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalAbelianExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open IntermediateField
open scoped commutatorElement
variable {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsGalois F Ω]

theorem GroundTheory.LocalField.exists_finite_abelian_mem {y : Ω} (hy : y ∈ maximalAbelianExtension F Ω) :
    ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsAbelianGalois F L ∧ y ∈ L := by sorry
