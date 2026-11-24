-- Prove2me | Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_mem_killedBy_iff
-- name    : GlobalTheory.PrimaryTorsionBlocks.mem_killedBy_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T18:53:47.212912+00:00
-- url     : https://prove2.me/theorems/6638685d-e691-4947-99dc-4b75ccb7ecb6
-- title:
--   Primary Torsion Blocks: mem killed By iff
-- statement:
--   The Primary Torsion Blocks construction uses the mem killed By iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowers.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/TorsionCountMultiplicativePrimePowers.lean#L23-L24

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

theorem GlobalTheory.PrimaryTorsionBlocks.mem_killedBy_iff {I : Ideal R} {x : M} : x ∈ killedBy (M := M) I ↔ I ≤ annOf x := by sorry
