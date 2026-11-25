-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_coordsVec_baseMap
-- name    : GroundTheory.Automorphic.Anisotropic.coordsVec_baseMap
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:21.727146+00:00
-- url     : https://prove2.me/theorems/ee00f0ae-648f-402b-8672-4dbe984e1f81
-- title:
--   Anisotropic: coords Vec base Map
-- statement:
--   The Anisotropic construction uses the coords Vec base Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L206-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L206-L209

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
variable {E : Type*} [CommRing E] [Algebra K E] (b : Module.Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {R}

theorem GroundTheory.Automorphic.Anisotropic.coordsVec_baseMap (f : R →ₐ[K] R') (x : ι → R ⊗[K] E) :
    coordsVec b R' (fun i => baseMap f (x i)) = f ∘ coordsVec b R x := by sorry
