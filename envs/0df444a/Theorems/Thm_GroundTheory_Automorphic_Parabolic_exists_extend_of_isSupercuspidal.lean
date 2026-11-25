-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_exists_extend_of_isSupercuspidal
-- name    : GroundTheory.Automorphic.Parabolic.exists_extend_of_isSupercuspidal
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T13:26:09.736706+00:00
-- url     : https://prove2.me/theorems/c137d788-ef77-522c-b4eb-79ea1a0b480d
-- title:
--   Parabolic: exists extend of is Supercuspidal
-- statement:
--   The Parabolic construction uses the exists extend of is Supercuspidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingProjective.lean#L195-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingProjective.lean#L195-L248

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingPositivity
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Function
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
variable {V U W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ (GL (Fin n) F) V}
  {ρ : Representation ℂ (GL (Fin n) F) U} {σ : Representation ℂ (GL (Fin n) F) W}
  {ω : GL (Fin n) F → ℂ}

theorem GroundTheory.Automorphic.Parabolic.exists_extend_of_isSupercuspidal [π.IsIrreducible] (hπ : IsSmooth π)
    (hsc : IsSupercuspidal π) (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (hωσ : HasCentralChar σ ω) (i : Representation.IntertwiningMap ρ σ) (hi : Injective i)
    (φ : Representation.IntertwiningMap ρ π) :
    ∃ Φ : Representation.IntertwiningMap σ π, Φ.comp i = φ := by sorry
