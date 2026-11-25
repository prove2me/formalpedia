-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_doubleCoset_affineWeylGL_injective
-- name    : GroundTheory.Automorphic.GLnLocal.doubleCoset_affineWeylGL_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:43.899922+00:00
-- url     : https://prove2.me/theorems/d7d05bbc-f263-4926-8d7b-81573a437097
-- title:
--   GLn Local: double Coset affine Weyl GL injective
-- statement:
--   The GLn Local construction uses the double Coset affine Weyl GL injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L598-L606
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L598-L606

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

theorem GroundTheory.Automorphic.GLnLocal.doubleCoset_affineWeylGL_injective {w w' : ExtendedAffineWeyl n} {g : GL (Fin n) F}
    (hw : g ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n))
    (hw' : g ∈ doubleCoset (affineWeylGL F n w') (iwahori F n) (iwahori F n)) : w = w' := by sorry
