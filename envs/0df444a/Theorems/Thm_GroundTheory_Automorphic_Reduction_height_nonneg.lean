-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_height_nonneg
-- name    : GroundTheory.Automorphic.Reduction.height_nonneg
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:04.142663+00:00
-- url     : https://prove2.me/theorems/d2c8485d-a469-552e-ad25-7215ea3b8c89
-- title:
--   Reduction: height nonneg
-- statement:
--   The Reduction construction uses the height nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L264-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L264-L265

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicGLn
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_IdeleNorms
import Definitions.Def_GroundTheory_AutomorphicForms_ReductionHeight
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
variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

theorem GroundTheory.Automorphic.Reduction.height_nonneg (g : AdelicGLn.AdelicGL K n) (x : Fin n → K) : 0 ≤ height g x := by sorry
