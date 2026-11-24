-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_HarishChandra_eq_zero_of_forall_highestWeight
-- name    : GroundTheory.Automorphic.HarishChandra.eq_zero_of_forall_highestWeight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:30:16.480207+00:00
-- url     : https://prove2.me/theorems/efa2e082-e7dc-4eb1-8b28-29e082bcfb75
-- title:
--   Harish Chandra: eq zero of forall highest Weight
-- statement:
--   The Harish Chandra construction uses the eq zero of forall highest Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L269-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HarishChandraCentre/Fischer.lean#L269-L339

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_RepBase
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_FischerForm
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraCentre_Fischer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.HarishChandra
open MvPolynomial
variable {n : ℕ}

theorem GroundTheory.Automorphic.HarishChandra.eq_zero_of_forall_highestWeight (T T' : Module.End ℂ (Poly n))
    (hcomm : ∀ i j, T * rowOp i j = rowOp i j * T)
    (hadj : ∀ f g, fischer (T f) g = fischer f (T' g))
    (hnormal : T * T' = T' * T)
    (hhw : ∀ (v : Poly n) (μ : Fin n → ℕ), (∀ i j, i < j → rowOp i j v = 0) → wtProj μ v = v →
      T v = 0) : T = 0 := by sorry
