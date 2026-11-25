-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_det_rmat_conjBase
-- name    : GroundTheory.Automorphic.Anisotropic.det_rmat_conjBase
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T02:57:25.923835+00:00
-- url     : https://prove2.me/theorems/f7209d97-3c9f-4903-98e0-df6e962a8952
-- title:
--   Anisotropic: det rmat conj Base
-- statement:
--   The Anisotropic construction uses the det rmat conj Base property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L177-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L177-L191

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

theorem GroundTheory.Automorphic.Anisotropic.det_rmat_conjBase (z : R ⊗[K] E) :
    (rmat b R (conjBase K E R z)).det = (rmat b R z).det := by sorry
