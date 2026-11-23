-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_blockHom_apply
-- name    : GroundTheory.Automorphic.Anisotropic.blockHom_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:05:34.574622+00:00
-- url     : https://prove2.me/theorems/61dc9e66-b80c-4e08-a66d-84250e15ac33
-- title:
--   Anisotropic: block Hom apply
-- statement:
--   The Anisotropic construction uses the block Hom apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L155-L156

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

theorem GroundTheory.Automorphic.Anisotropic.blockHom_apply (M : Matrix ι ι (R ⊗[K] E)) (i j : ι) (k l : κ) :
    blockHom b R M (i, k) (j, l) = rmat b R (M i j) k l := by sorry
