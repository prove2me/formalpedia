-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_bijective_mk_affineWeylGL
-- name    : GroundTheory.Automorphic.GLnLocal.bijective_mk_affineWeylGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:52:50.909824+00:00
-- url     : https://prove2.me/theorems/2a0faf13-ba58-5288-bb8a-006c41557c5f
-- title:
--   GLn Local: bijective mk affine Weyl GL
-- statement:
--   The GLn Local construction uses the bijective mk affine Weyl GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L628-L639
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L628-L639

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLocal
import Definitions.Def_GroundTheory_AutomorphicForms_GLnLattice
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_AffineBruhat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Matrix DoubleCoset ValuativeRel
open GroundTheory.Automorphic.GLnLocal
variable (F : Type*) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  (n : ℕ)
local notation "ϖ" => ((uniformizer F : 𝒪[F]) : F)

theorem GroundTheory.Automorphic.GLnLocal.bijective_mk_affineWeylGL :
    Function.Bijective fun w : ExtendedAffineWeyl n =>
      DoubleCoset.mk (iwahori F n) (iwahori F n) (affineWeylGL F n w) := by sorry
