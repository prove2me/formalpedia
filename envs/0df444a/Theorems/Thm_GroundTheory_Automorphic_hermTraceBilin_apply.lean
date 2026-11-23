-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hermTraceBilin_apply
-- name    : GroundTheory.Automorphic.hermTraceBilin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:31:26.324799+00:00
-- url     : https://prove2.me/theorems/45f3a6e2-4754-4ca6-8a00-8e402ea100d6
-- title:
--   Automorphic: herm Trace Bilin apply
-- statement:
--   The Automorphic construction uses the herm Trace Bilin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L131-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L131-L132

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

theorem GroundTheory.Automorphic.hermTraceBilin_apply (x y : ι → R ⊗[K] E) : hermTraceBilin K H R x y = hermTrace K H R x y := by sorry

attribute [defeq] GroundTheory.Automorphic.hermTraceBilin_apply
