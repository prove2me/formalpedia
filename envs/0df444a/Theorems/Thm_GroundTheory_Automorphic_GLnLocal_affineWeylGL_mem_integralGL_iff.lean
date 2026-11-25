-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_mem_integralGL_iff
-- name    : GroundTheory.Automorphic.GLnLocal.affineWeylGL_mem_integralGL_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:30:08.849355+00:00
-- url     : https://prove2.me/theorems/01dffcec-b308-4df3-8536-d940426c024e
-- title:
--   GLn Local: affine Weyl GL mem integral GL iff
-- statement:
--   The GLn Local construction uses the affine Weyl GL mem integral GL iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L663-L697
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L663-L697

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

theorem GroundTheory.Automorphic.GLnLocal.affineWeylGL_mem_integralGL_iff (w : ExtendedAffineWeyl n) :
    affineWeylGL F n w ∈ integralGL F n ↔ w.left = 1 := by sorry
