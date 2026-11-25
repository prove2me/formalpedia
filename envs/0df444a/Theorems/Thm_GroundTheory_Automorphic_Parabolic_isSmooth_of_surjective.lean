-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isSmooth_of_surjective
-- name    : GroundTheory.Automorphic.Parabolic.isSmooth_of_surjective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:28:56.168453+00:00
-- url     : https://prove2.me/theorems/04d022a6-f522-4479-abc1-3cbc98e3b009
-- title:
--   Parabolic: is Smooth of surjective
-- statement:
--   The Parabolic construction uses the is Smooth of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingProjective.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingProjective.lean#L31-L37

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

theorem GroundTheory.Automorphic.Parabolic.isSmooth_of_surjective (hρ : IsSmooth ρ) (p : Representation.IntertwiningMap ρ σ)
    (hp : Surjective p) : IsSmooth σ := by sorry
