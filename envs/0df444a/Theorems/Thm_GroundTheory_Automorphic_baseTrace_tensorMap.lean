-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_baseTrace_tensorMap
-- name    : GroundTheory.Automorphic.baseTrace_tensorMap
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:00.117639+00:00
-- url     : https://prove2.me/theorems/718b01f9-cf47-43f5-8190-28474ee93236
-- title:
--   Automorphic: base Trace tensor Map
-- statement:
--   The Automorphic construction uses the base Trace tensor Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L45-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L45-L50

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
variable (K E) (R : Type*) [CommRing R] [Algebra K R]
variable {K E R}
omit [Algebra.IsQuadraticExtension K E]

theorem GroundTheory.Automorphic.baseTrace_tensorMap {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (z : R ⊗[K] E) : baseTrace K E S (tensorMap E f z) = f (baseTrace K E R z) := by sorry
