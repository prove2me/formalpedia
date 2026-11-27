-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_PeterssonComplement_disjoint_orthIn
-- name    : GroundTheory.Automorphic.PeterssonComplement.disjoint_orthIn
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:53.286043+00:00
-- url     : https://prove2.me/theorems/f9cf97d0-f122-4b36-81eb-9d28e6012944
-- title:
--   Petersson Complement: disjoint orth In
-- statement:
--   The Petersson Complement construction uses the disjoint orth In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L25-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/TensorProductTheorem/PeterssonComplement.lean#L25-L30

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_TensorProductTheorem_PeterssonComplement
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
open GroundTheory.Automorphic.PeterssonComplement
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H)
variable {ι}

theorem GroundTheory.Automorphic.PeterssonComplement.disjoint_orthIn (hι : Function.Injective ι) (U : Submodule ℂ V) : Disjoint U (orthIn ι U) := by sorry
