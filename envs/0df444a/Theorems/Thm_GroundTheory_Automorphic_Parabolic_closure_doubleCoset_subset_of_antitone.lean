-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_closure_doubleCoset_subset_of_antitone
-- name    : GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:48.977784+00:00
-- url     : https://prove2.me/theorems/ab5cc3f0-427a-54e5-89fe-2b216ebef15d
-- title:
--   Parabolic: closure double Coset subset of antitone
-- statement:
--   The Parabolic construction uses the closure double Coset subset of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L160-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L160-L179

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCells
import Definitions.Def_GroundTheory_AutomorphicForms_InductionParabolic
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaFiltration
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
open Matrix Iwasawa Topology Set DoubleCoset
variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [T1Space F] {n : ℕ}
  {β γ : Fin n → ℕ}

theorem GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone {k : ℕ} {w : Fin k → Equiv.Perm (Fin n)}
    (hcov : ∀ g : GL (Fin n) F, ∃! j, g ∈ doubleCoset (permGL F (w j))
      (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ))
    (hanti : Antitone fun j => cellHeight β γ (permGL F (w j))) (j : Fin k) :
    closure (doubleCoset (permGL F (w j)) (blockUpper F n β : Set (GL (Fin n) F))
        (blockUpper F n γ)) ⊆
      ⋃ l : Fin k, ⋃ (_ : j ≤ l), doubleCoset (permGL F (w l))
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ) := by sorry
