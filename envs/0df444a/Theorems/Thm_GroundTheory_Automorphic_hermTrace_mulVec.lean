-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermTrace_mulVec
-- name    : GroundTheory.Automorphic.hermTrace_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:54:07.063565+00:00
-- url     : https://prove2.me/theorems/3669b680-b57a-54f0-a334-a3524af36c93
-- title:
--   Automorphic: herm Trace mul Vec
-- statement:
--   The Automorphic construction uses the herm Trace mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L150-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L150-L152

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
variable [DecidableEq ι]

theorem GroundTheory.Automorphic.hermTrace_mulVec (g : unitaryPoints K E H R) (x y : ι → R ⊗[K] E) :
    hermTrace K H R (unitaryMat g *ᵥ x) (unitaryMat g *ᵥ y) = hermTrace K H R x y := by sorry
