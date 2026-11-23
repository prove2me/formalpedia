-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GLnLocal_affineWeylGL_inr
-- name    : GroundTheory.Automorphic.GLnLocal.affineWeylGL_inr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:40:28.653667+00:00
-- url     : https://prove2.me/theorems/3022ce0d-1532-48c2-bf93-ec3fcc89250a
-- title:
--   GLn Local: affine Weyl GL inr
-- statement:
--   The GLn Local construction uses the affine Weyl GL inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L645-L647
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AffineBruhat.lean#L645-L647

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

theorem GroundTheory.Automorphic.GLnLocal.affineWeylGL_inr (σ : Equiv.Perm (Fin n)) :
    affineWeylGL F n (SemidirectProduct.inr σ) = permGL F σ := by sorry
