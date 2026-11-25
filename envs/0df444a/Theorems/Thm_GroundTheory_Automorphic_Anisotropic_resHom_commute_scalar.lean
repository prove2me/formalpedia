-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_resHom_commute_scalar
-- name    : GroundTheory.Automorphic.Anisotropic.resHom_commute_scalar
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T13:02:56.487453+00:00
-- url     : https://prove2.me/theorems/74d2c4c1-0f7d-5b64-a5f5-f828f03addf9
-- title:
--   Anisotropic: res Hom commute scalar
-- statement:
--   The Anisotropic construction uses the res Hom commute scalar property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L110-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L110-L112

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

theorem GroundTheory.Automorphic.Anisotropic.resHom_commute_scalar (M : Matrix ι ι (R ⊗[K] E)) (s : R ⊗[K] E) :
    resHom b R M * resHom b R (Matrix.scalar ι s) = resHom b R (Matrix.scalar ι s) * resHom b R M := by sorry
