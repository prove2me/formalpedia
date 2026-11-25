-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_blockAssemble_apply
-- name    : GroundTheory.Automorphic.Parabolic.blockAssemble_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:31:11.958904+00:00
-- url     : https://prove2.me/theorems/244546d8-292c-5f87-a386-821a9e2f866b
-- title:
--   Parabolic: block Assemble apply
-- statement:
--   The Parabolic construction uses the block Assemble apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/LeviCartan.lean#L62-L65

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

theorem GroundTheory.Automorphic.Parabolic.blockAssemble_apply (X : ∀ a : Set.range β, Matrix (Fiber β a) (Fiber β a) R)
    (i j : Fin n) :
    blockAssemble β R X i j = blockDiagonal' X ((Equiv.sigmaFiberEquiv (blockOf β)).symm i)
      ((Equiv.sigmaFiberEquiv (blockOf β)).symm j) := by sorry
