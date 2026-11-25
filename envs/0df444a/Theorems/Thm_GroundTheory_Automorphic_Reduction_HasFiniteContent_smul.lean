-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Reduction_HasFiniteContent_smul
-- name    : GroundTheory.Automorphic.Reduction.HasFiniteContent.smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T01:07:15.209816+00:00
-- url     : https://prove2.me/theorems/946c1229-c71e-4529-83ee-c1eb321afb70
-- title:
--   Has Finite Content: smul
-- statement:
--   The Has Finite Content construction uses the smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L137-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ReductionHeight.lean#L137-L140

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

theorem GroundTheory.Automorphic.Reduction.HasFiniteContent.smul {y : Fin n → 𝔸[K]} (hy : HasFiniteContent y)
    (s : GroundTheory.Global.IdeleGroup K) : HasFiniteContent ((s : 𝔸[K]) • y) := by sorry
