-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_cellUnion_mul_mem
-- name    : GroundTheory.Automorphic.Parabolic.cellUnion_mul_mem
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T13:31:48.977921+00:00
-- url     : https://prove2.me/theorems/fd720681-df95-47ff-868d-4b0b973e52f3
-- title:
--   Parabolic: cell Union mul mem
-- statement:
--   The Parabolic construction uses the cell Union mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaUnnormalized.lean#L21-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaUnnormalized.lean#L21-L39

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaGraded
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellKernel
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellSurjective
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaUnnormalized
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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)

theorem GroundTheory.Automorphic.Parabolic.cellUnion_mul_mem {k : ℕ} (w : Fin k → Equiv.Perm (Fin n)) (j : ℕ) :
    (∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) j, ∀ q ∈ blockUpper F n γ, g * q ∈ cellUnion (fun l => doubleCoset
          (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j) ∧
      (∀ p ∈ blockUpper F n β, ∀ g ∈ cellUnion (fun l => doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) j, p * g ∈ cellUnion
          (fun l => doubleCoset (permGL F (w l)) (blockUpper F n β : Set (GL (Fin n) F))
            (blockUpper F n γ)) j) := by sorry
