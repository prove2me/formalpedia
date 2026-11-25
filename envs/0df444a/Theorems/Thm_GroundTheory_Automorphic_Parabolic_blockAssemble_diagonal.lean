-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_diagonal
-- name    : GroundTheory.Automorphic.Parabolic.blockAssemble_diagonal
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:31:24.981347+00:00
-- url     : https://prove2.me/theorems/04996650-e164-4fff-a0e8-a7c354f7d5e1
-- title:
--   Parabolic: block Assemble diagonal
-- statement:
--   The Parabolic construction uses the block Assemble diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L93-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L93-L105

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdmissibleInduction
import Definitions.Def_GroundTheory_AutomorphicForms_Cartan
import Definitions.Def_GroundTheory_AutomorphicForms_LeviCartan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel
variable {n : ℕ} {α : Type*} [LinearOrder α] (β : Fin n → α)
variable (R : Type*) [CommRing R]
variable {β R}

theorem GroundTheory.Automorphic.Parabolic.blockAssemble_diagonal (d : ∀ a : Set.range β, Fiber β a → R) :
    blockAssemble β R (fun a => diagonal (d a)) =
      diagonal fun i => d (blockOf β i) ⟨i, rfl⟩ := by sorry
