-- Prove2me | Theorems.Thm_GlobalTheory_EquivariantSubspace_smoothOnH_zero
-- name    : GlobalTheory.EquivariantSubspace.smoothOnH_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T03:59:51.495913+00:00
-- url     : https://prove2.me/theorems/32f377c3-659b-4a6e-9af5-71e06b4faddf
-- title:
--   Equivariant Subspace: smooth On H zero
-- statement:
--   The Equivariant Subspace construction uses the smooth On H zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EquivariantSubspace.lean#L12-L14

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

theorem GlobalTheory.EquivariantSubspace.smoothOnH_zero (H : Matrix (Fin n) (Fin n) ℂ) :
    SmoothOnH H (0 : Matrix (Fin n) (Fin n) ℂ → E) := by sorry
