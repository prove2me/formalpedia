-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_exists_rationalGL_mul_siegelSet_eq_univ
-- name    : GroundTheory.Automorphic.Reduction.exists_rationalGL_mul_siegelSet_eq_univ
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:59:49.193795+00:00
-- url     : https://prove2.me/theorems/f330f242-f8e4-5c18-a014-0b653a0d503c
-- title:
--   Reduction: exists rational GL mul siegel Set eq univ
-- statement:
--   The Reduction construction uses the exists rational GL mul siegel Set eq univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L322-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionSiegel.lean#L322-L329

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionCore
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionSiegel
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
open GroundTheory.Global GroundTheory.Global.IdeleGroup
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Reduction
variable {K : Type*} [Field K] [NumberField K]
open scoped Pointwise

theorem GroundTheory.Automorphic.Reduction.exists_rationalGL_mul_siegelSet_eq_univ (n : ℕ) :
    ∃ ω : Set (AdelicGLn.AdelicGL K n), IsCompact ω ∧
      ω ⊆ (adelicBorel (K := K) (n := n) : Set (AdelicGLn.AdelicGL K n)) ∧ ∃ t : ℝ, 0 < t ∧
        (AdelicGLn.rationalGL K n : Set (AdelicGLn.AdelicGL K n)) * siegelSet n ω t = univ := by sorry
