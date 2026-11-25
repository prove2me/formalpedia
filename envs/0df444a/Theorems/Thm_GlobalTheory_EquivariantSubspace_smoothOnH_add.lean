-- Prove2me | Theorems.Thm_GlobalTheory_EquivariantSubspace_smoothOnH_add
-- name    : GlobalTheory.EquivariantSubspace.smoothOnH_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:31.839911+00:00
-- url     : https://prove2.me/theorems/b5c96df1-1e7a-426a-93e9-6dd6ddf94dea
-- title:
--   Equivariant Subspace: smooth On H add
-- statement:
--   The Equivariant Subspace construction uses the smooth On H add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L16-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L16-L24

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

theorem GlobalTheory.EquivariantSubspace.smoothOnH_add {H : Matrix (Fin n) (Fin n) ℂ} {f f' : Matrix (Fin n) (Fin n) ℂ → E}
    (hf : SmoothOnH H f) (hf' : SmoothOnH H f') : SmoothOnH H (f + f') := by sorry
