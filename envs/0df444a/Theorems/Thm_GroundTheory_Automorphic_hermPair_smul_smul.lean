-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermPair_smul_smul
-- name    : GroundTheory.Automorphic.hermPair_smul_smul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:01.622834+00:00
-- url     : https://prove2.me/theorems/4239df65-af8e-5e4f-8b7a-d55f4ee012db
-- title:
--   Automorphic: herm Pair smul smul
-- statement:
--   The Automorphic construction uses the herm Pair smul smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L210-L212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L210-L212

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_AdelicUnitaryGroups_Anisotropic
import Definitions.Def_GroundTheory_AutomorphicForms_DefiniteClassNumber_HermTraceSelfOfHermValue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Automorphic
open Module Matrix TensorProduct
variable {K E : Type*} [Field K] [CommRing E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] (H : Matrix ι ι E)
variable (K) (R : Type*) [CommRing R] [Algebra K R]
variable {K H R}

theorem GroundTheory.Automorphic.hermPair_smul_smul (c : R ⊗[K] E) (x y : ι → R ⊗[K] E) :
    hermPair K H R (c • x) (c • y) = (conjBase K E R c * c) * hermPair K H R x y := by sorry
