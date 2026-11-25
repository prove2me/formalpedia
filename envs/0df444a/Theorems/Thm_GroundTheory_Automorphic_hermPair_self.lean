-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermPair_self
-- name    : GroundTheory.Automorphic.hermPair_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:12.559938+00:00
-- url     : https://prove2.me/theorems/eed8cff6-dfd4-4626-8e1b-d087df596e04
-- title:
--   Automorphic: herm Pair self
-- statement:
--   The Automorphic construction uses the herm Pair self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L65-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L65-L65

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

theorem GroundTheory.Automorphic.hermPair_self (x : ι → R ⊗[K] E) : hermPair K H R x x = hermValue K H R x := by sorry
