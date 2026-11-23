-- Prove2me | Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_mem_annOf
-- name    : GlobalTheory.PrimaryTorsionBlocks.mem_annOf
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:10:18.112858+00:00
-- url     : https://prove2.me/theorems/fd4b48f2-f098-4646-9ba7-15b24187be09
-- title:
--   Primary Torsion Blocks: mem ann Of
-- statement:
--   The Primary Torsion Blocks construction uses the mem ann Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowers.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowers.lean#L20-L21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PrimaryTorsionBlocks
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

theorem GlobalTheory.PrimaryTorsionBlocks.mem_annOf {x : M} {a : R} : a ∈ annOf x ↔ a • x = 0 := by sorry
