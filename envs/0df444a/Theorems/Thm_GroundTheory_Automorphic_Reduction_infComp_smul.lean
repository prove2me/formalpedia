-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_infComp_smul
-- name    : GroundTheory.Automorphic.Reduction.infComp_smul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T01:09:13.213564+00:00
-- url     : https://prove2.me/theorems/c0ff32d6-cf63-450e-9fc7-a9fc1f6dfae1
-- title:
--   Reduction: inf Comp smul
-- statement:
--   The Reduction construction uses the inf Comp smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L134-L135
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L134-L135

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

theorem GroundTheory.Automorphic.Reduction.infComp_smul (w : InfinitePlace K) (s : 𝔸[K]) (y : Fin n → 𝔸[K]) :
    infComp w (s • y) = s.1 w • infComp w y := by sorry
