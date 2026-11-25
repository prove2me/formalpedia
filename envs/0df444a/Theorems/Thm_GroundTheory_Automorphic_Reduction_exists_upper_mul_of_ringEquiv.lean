-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_upper_mul_of_ringEquiv
-- name    : GroundTheory.Automorphic.Reduction.exists_upper_mul_of_ringEquiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:12:24.717819+00:00
-- url     : https://prove2.me/theorems/86e1d4d0-870b-543d-9351-5f8cba6bdd33
-- title:
--   Reduction: exists upper mul of ring Equiv
-- statement:
--   The Reduction construction uses the exists upper mul of ring Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L46-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionIwasawa.lean#L46-L94

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_RealGroupsIwasawa
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_UnitBound
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionIwasawa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Topology Filter Set Matrix
open scoped NumberField.AdeleRing RestrictedProduct
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {E 𝕜 : Type*} [NormedField E] [RCLike 𝕜] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.exists_upper_mul_of_ringEquiv (φ : E ≃+* 𝕜) (hφ : ∀ x, ‖φ x‖ = ‖x‖) (h : GL (Fin n) E) :
    ∃ b : GL (Fin n) E, (b : Matrix (Fin n) (Fin n) E).IsUpperTriangular ∧
      ∃ k : GL (Fin n) E, (∀ y : Fin n → E,
        euclidNorm (y ᵥ* (k : Matrix (Fin n) (Fin n) E)) = euclidNorm y) ∧ h = b * k := by sorry
