-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_lmat_eq_rmat
-- name    : GroundTheory.Automorphic.Anisotropic.lmat_eq_rmat
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:32.060177+00:00
-- url     : https://prove2.me/theorems/9902e186-bde9-4bf2-b818-89eba6c107fa
-- title:
--   Anisotropic: lmat eq rmat
-- statement:
--   The Anisotropic construction uses the lmat eq rmat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L148-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicRestrict.lean#L148-L150

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

theorem GroundTheory.Automorphic.Anisotropic.lmat_eq_rmat (a : R ⊗[K] E) : lmat b R a = rmat b R a := by sorry
