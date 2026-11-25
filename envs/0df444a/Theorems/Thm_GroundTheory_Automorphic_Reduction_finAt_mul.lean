-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_finAt_mul
-- name    : GroundTheory.Automorphic.Reduction.finAt_mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:06:19.531992+00:00
-- url     : https://prove2.me/theorems/358f2ab2-ee2e-4b16-82a1-9be3c12d65cf
-- title:
--   Reduction: fin At mul
-- statement:
--   The Reduction construction uses the fin At mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L74-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L74-L76

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

theorem GroundTheory.Automorphic.Reduction.finAt_mul (v : HeightOneSpectrum (𝓞 K)) (g h : AdelicGLn.AdelicGL K n) :
    finAt v (g * h) = finAt v g * finAt v h := by sorry
