-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Parabolic_disjoint_cellUnion
-- name    : GroundTheory.Automorphic.Parabolic.disjoint_cellUnion
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:23:23.799427+00:00
-- url     : https://prove2.me/theorems/f9ba91f9-6d22-4452-a574-2a6b3d2c5773
-- title:
--   Parabolic: disjoint cell Union
-- statement:
--   The Parabolic construction uses the disjoint cell Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L100-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaFiltration.lean#L100-L105

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
omit [TopologicalSpace X] hcov hcl

theorem GroundTheory.Automorphic.Parabolic.disjoint_cellUnion (j : Fin k) : Disjoint (C j) (cellUnion C j) := by sorry
