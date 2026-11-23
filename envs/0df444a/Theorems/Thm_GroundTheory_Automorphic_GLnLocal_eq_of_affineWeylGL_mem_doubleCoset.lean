-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_eq_of_affineWeylGL_mem_doubleCoset
-- name    : GroundTheory.Automorphic.GLnLocal.eq_of_affineWeylGL_mem_doubleCoset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:35:02.177316+00:00
-- url     : https://prove2.me/theorems/605e5f7e-b53f-474e-b10b-1cda58aaeb94
-- title:
--   GLn Local: eq of affine Weyl GL mem double Coset
-- statement:
--   The GLn Local construction uses the eq of affine Weyl GL mem double Coset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L253-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L253-L282

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

theorem GroundTheory.Automorphic.GLnLocal.eq_of_affineWeylGL_mem_doubleCoset {w w' : ExtendedAffineWeyl n}
    (h : affineWeylGL F n w' ∈ doubleCoset (affineWeylGL F n w) (iwahori F n) (iwahori F n)) :
    w = w' := by sorry
