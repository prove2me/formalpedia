-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_conjBase_smul
-- name    : GroundTheory.Automorphic.conjBase_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:41:09.369366+00:00
-- url     : https://prove2.me/theorems/0810edc6-64f2-4679-8f5b-a30789c3811c
-- title:
--   Automorphic: conj Base smul
-- statement:
--   The Automorphic construction uses the conj Base smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Anisotropic.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Anisotropic.lean#L36-L39

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Topology
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct Topology Metric
noncomputable section
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (K) (H : Matrix ι ι E) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}

theorem GroundTheory.Automorphic.conjBase_smul (c : R) (z : R ⊗[K] E) :
    conjBase K E R (c • z) = c • conjBase K E R z := by sorry
