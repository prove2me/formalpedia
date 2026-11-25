-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_IsSchwartzBruhat_exists_congruence_invariant
-- name    : GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.exists_congruence_invariant
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:26:12.846642+00:00
-- url     : https://prove2.me/theorems/d2430bfa-8852-4624-bb66-1a3a2454c58e
-- title:
--   Is Schwartz Bruhat: exists congruence invariant
-- statement:
--   The Is Schwartz Bruhat construction uses the exists congruence invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L168-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/ExistsEqPowMulOfValuationLe.lean#L168-L224

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJZetaDefs
import Definitions.Def_GroundTheory_AutomorphicForms_MeasuresGL
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_ExistsEqPowMulOfValuationLe
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
open GroundTheory.Automorphic.GodementJacquet
open Matrix GLnLocal ValuativeRel Topology Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

theorem GroundTheory.Automorphic.GodementJacquet.IsSchwartzBruhat.exists_congruence_invariant {Φ : Matrix (Fin n) (Fin n) F → ℂ}
    (hΦ : IsSchwartzBruhat Φ) :
    ∃ m : ℕ, ∀ k ∈ congruenceSubgroup F n m, ∀ X : Matrix (Fin n) (Fin n) F,
      Φ ((k : Matrix (Fin n) (Fin n) F) * X) = Φ X ∧ Φ (X * (k : Matrix (Fin n) (Fin n) F)) = Φ X := by sorry
