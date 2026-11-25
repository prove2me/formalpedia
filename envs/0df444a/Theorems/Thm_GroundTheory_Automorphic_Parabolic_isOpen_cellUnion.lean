-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_isOpen_cellUnion
-- name    : GroundTheory.Automorphic.Parabolic.isOpen_cellUnion
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:41.244842+00:00
-- url     : https://prove2.me/theorems/d491f5ee-efbb-40d4-a1e4-99143174ed76
-- title:
--   Parabolic: is Open cell Union
-- statement:
--   The Parabolic construction uses the is Open cell Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L56-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L56-L77

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
variable {X : Type*} {k : ℕ} (C : Fin k → Set X)
variable {C}
variable [TopologicalSpace X]
variable (hdisj : Pairwise fun i j => Disjoint (C i) (C j)) (hcov : ∀ x, ∃ l, x ∈ C l)
  (hcl : ∀ j, closure (C j) ⊆ ⋃ l : Fin k, ⋃ (_ : j ≤ l), C l)
include hdisj hcov hcl

theorem GroundTheory.Automorphic.Parabolic.isOpen_cellUnion (j : ℕ) : IsOpen (cellUnion C j) := by sorry
