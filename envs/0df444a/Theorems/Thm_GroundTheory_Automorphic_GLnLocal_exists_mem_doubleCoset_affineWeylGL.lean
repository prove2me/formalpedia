-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_exists_mem_doubleCoset_affineWeylGL
-- name    : GroundTheory.Automorphic.GLnLocal.exists_mem_doubleCoset_affineWeylGL
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:34:39.81583+00:00
-- url     : https://prove2.me/theorems/693dd61f-330a-40d7-bd26-132c2ddf94e1
-- title:
--   GLn Local: exists mem double Coset affine Weyl GL
-- statement:
--   The GLn Local construction uses the exists mem double Coset affine Weyl GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L584-L592
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L584-L592

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

theorem GroundTheory.Automorphic.GLnLocal.exists_mem_doubleCoset_affineWeylGL (g : GL (Fin n) F) :
    ∃ w : ExtendedAffineWeyl n,
      g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n) := by sorry
