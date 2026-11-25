-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Anisotropic_ofResVec_smul
-- name    : GroundTheory.Automorphic.Anisotropic.ofResVec_smul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:28.365188+00:00
-- url     : https://prove2.me/theorems/42faec10-68ff-5290-bb0e-ed2670a4d1e5
-- title:
--   Anisotropic: of Res Vec smul
-- statement:
--   The Anisotropic construction uses the of Res Vec smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L52-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/AnisotropicUnitaryRes.lean#L52-L56

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

theorem GroundTheory.Automorphic.Anisotropic.ofResVec_smul (t : R) (y : Fin 𝒩 → R) : ofResVec b R (t • y) = t • ofResVec b R y := by sorry
