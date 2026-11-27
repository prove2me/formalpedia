-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_pairwise_disjoint_doubleCoset_affineWeylGL
-- name    : GroundTheory.Automorphic.GLnLocal.pairwise_disjoint_doubleCoset_affineWeylGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:52:28.843798+00:00
-- url     : https://prove2.me/theorems/16a7e8ab-9113-53bc-987c-e3f1f2c479ec
-- title:
--   GLn Local: pairwise disjoint double Coset affine Weyl GL
-- statement:
--   The GLn Local construction uses the pairwise disjoint double Coset affine Weyl GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L620-L626
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L620-L626

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

theorem GroundTheory.Automorphic.GLnLocal.pairwise_disjoint_doubleCoset_affineWeylGL :
    Pairwise (Function.onFun Disjoint fun w : ExtendedAffineWeyl n =>
      doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) := by sorry
