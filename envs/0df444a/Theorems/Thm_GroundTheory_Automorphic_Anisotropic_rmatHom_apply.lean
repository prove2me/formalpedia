-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_rmatHom_apply
-- name    : GroundTheory.Automorphic.Anisotropic.rmatHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:04:29.0804+00:00
-- url     : https://prove2.me/theorems/19752be7-6583-4648-a01c-5eb5ce524312
-- title:
--   Anisotropic: rmat Hom apply
-- statement:
--   The Anisotropic construction uses the rmat Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L76-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L76-L76

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

theorem GroundTheory.Automorphic.Anisotropic.rmatHom_apply (x : R ⊗[K] A) : rmatHom b R x = rmat b R x := by sorry

attribute [defeq] GroundTheory.Automorphic.Anisotropic.rmatHom_apply
