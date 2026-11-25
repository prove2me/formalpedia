-- Prove2me | Theorems.Thm_GlobalTheory_EquivariantSubspace_smoothOnH_smul
-- name    : GlobalTheory.EquivariantSubspace.smoothOnH_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:53.240277+00:00
-- url     : https://prove2.me/theorems/a259afea-321a-4db2-8760-0b01547436d5
-- title:
--   Equivariant Subspace: smooth On H smul
-- statement:
--   The Equivariant Subspace construction uses the smooth On H smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L26-L32

import Mathlib
import Definitions.Def_Formalism_FormalDegreeBessel_StatementRP
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EquivariantSubspace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.QuantumDeterminants
open GlobalTheory GlobalTheory.EquivariantSubspace
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GlobalTheory.EquivariantSubspace.smoothOnH_smul {H : Matrix (Fin n) (Fin n) ℂ} {f : Matrix (Fin n) (Fin n) ℂ → E} (a : ℂ)
    (hf : SmoothOnH H f) : SmoothOnH H (a • f) := by sorry
