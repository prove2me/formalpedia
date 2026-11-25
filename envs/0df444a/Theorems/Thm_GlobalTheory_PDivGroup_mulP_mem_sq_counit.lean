-- Prove2me | Theorems.Thm_GlobalTheory_PDivGroup_mulP_mem_sq_counit
-- name    : GlobalTheory.PDivGroup.mulP_mem_sq_counit
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T04:35:36.334089+00:00
-- url     : https://prove2.me/theorems/954b759d-9b57-4643-8e2e-081742502e9e
-- title:
--   PDiv Group: mul P mem sq counit
-- statement:
--   The PDiv Group construction uses the mul P mem sq counit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulPMemSqCounitKer.lean#L13-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MulPMemSqCounitKer.lean#L13-L141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SquarePresentationOfCounitalComulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocalFactorAtAugmentationCounitalComulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPresentationSquareAtPointOfLocalFactorStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftSquarePresentationOfFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CotangentMapInjectiveOfSquarePresentationAtPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPFlatStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PDivGroupMulPUnitFibreEqLevelOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NatCastSmulMemAugIdealSqSupMapMulPStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MulPMemSqCounitKer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.mulP_mem_sq_counit : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O], (p : O) ≠ 0 → ¬IsUnit (p : O) → (∀ a : O, ∃ b : O, b ^ p = a) → ∀ (G : GlobalTheory.PDivGroup p O) (n : ℕ) (b : G.A n), G.mulP n b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A (n + 1))) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom O (G.A n)) ^ 2 := by sorry
