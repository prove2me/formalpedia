-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_conjBase_det_mul_det
-- name    : GroundTheory.Automorphic.Anisotropic.conjBase_det_mul_det
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T04:26:11.846836+00:00
-- url     : https://prove2.me/theorems/bf44fcd6-4020-47d5-8827-c758f90af382
-- title:
--   Anisotropic: conj Base det mul det
-- statement:
--   The Anisotropic construction uses the conj Base det mul det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L193-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L193-L206

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicRestrict
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups
import Definitions.Def_GroundTheory_AutomorphicForms_AnisotropicUnitaryRes
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open Module Matrix TensorProduct
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Automorphic
noncomputable section
open GroundTheory.Automorphic.Anisotropic
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] [DecidableEq κ] (b : Basis κ K E)
variable (R : Type*) [CommRing R] [Algebra K R] {R' : Type*} [CommRing R'] [Algebra K R']
local notation "𝒩" => Fintype.card (ι × κ)
variable {R}
variable (R)
variable {R}
variable (R)

theorem GroundTheory.Automorphic.Anisotropic.conjBase_det_mul_det (H : Matrix ι ι E) (hH : IsUnit H.det) (g : unitaryPoints K E H R) :
    conjBase K E R ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det * ((g : GL ι (R ⊗[K] E)) : Matrix ι ι (R ⊗[K] E)).det = 1 := by sorry
