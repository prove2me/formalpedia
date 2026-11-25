-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmat_baseMap
-- name    : GroundTheory.Automorphic.Anisotropic.rmat_baseMap
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:24.800807+00:00
-- url     : https://prove2.me/theorems/4447624a-9d8e-4b0a-b386-61541d1d68b7
-- title:
--   Anisotropic: rmat base Map
-- statement:
--   The Anisotropic construction uses the rmat base Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L134-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L134-L138

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

theorem GroundTheory.Automorphic.Anisotropic.rmat_baseMap (f : R →ₐ[K] R') (x : R ⊗[K] A) :
    rmat b R' (baseMap f x) = (rmat b R x).map f := by sorry
