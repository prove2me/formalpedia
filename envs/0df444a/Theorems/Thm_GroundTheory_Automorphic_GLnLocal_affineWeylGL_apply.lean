-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_apply
-- name    : GroundTheory.Automorphic.GLnLocal.affineWeylGL_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:52.779148+00:00
-- url     : https://prove2.me/theorems/9ea0dba5-166d-4e28-9290-96404860752c
-- title:
--   GLn Local: affine Weyl GL apply
-- statement:
--   The GLn Local construction uses the affine Weyl GL apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L202-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L202-L207

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

theorem GroundTheory.Automorphic.GLnLocal.affineWeylGL_apply (w : ExtendedAffineWeyl n) (i j : Fin n) :
    (affineWeylGL F n w : Matrix (Fin n) (Fin n) F) i j =
      if i = w.right j then ϖ ^ (w.left i).toAdd else 0 := by sorry
