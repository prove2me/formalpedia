-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermValue_smul
-- name    : GroundTheory.Automorphic.hermValue_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:09.526473+00:00
-- url     : https://prove2.me/theorems/817a3e32-5c97-5a59-8fba-54b0355081a4
-- title:
--   Automorphic: herm Value smul
-- statement:
--   The Automorphic construction uses the herm Value smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Anisotropic.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AdelicUnitaryGroups/Anisotropic.lean#L41-L47

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

theorem GroundTheory.Automorphic.hermValue_smul (c : R) (x : ι → R ⊗[K] E) :
    hermValue K H R (c • x) = (c * c) • hermValue K H R x := by sorry
