-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_baseMap_baseBasis
-- name    : GroundTheory.Automorphic.Anisotropic.baseMap_baseBasis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:00.062539+00:00
-- url     : https://prove2.me/theorems/d9a0d0d9-729b-4716-a488-54e95bfa8d21
-- title:
--   Anisotropic: base Map base Basis
-- statement:
--   The Anisotropic construction uses the base Map base Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L113-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L113-L116

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K : Type*} [Field K] {κ : Type*} [Fintype κ] [DecidableEq κ]
variable {A : Type*} [Ring A] [Algebra K A] (b : Module.Basis κ K A)
variable (R : Type*) [CommRing R] [Algebra K R]
variable {R} {R' : Type*} [CommRing R'] [Algebra K R']

theorem GroundTheory.Automorphic.Anisotropic.baseMap_baseBasis (f : R →ₐ[K] R') (k : κ) :
    baseMap f (baseBasis b R k) = baseBasis b R' k := by sorry
