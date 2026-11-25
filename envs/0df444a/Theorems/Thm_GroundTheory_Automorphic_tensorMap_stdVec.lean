-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tensorMap_stdVec
-- name    : GroundTheory.Automorphic.tensorMap_stdVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:30.055134+00:00
-- url     : https://prove2.me/theorems/b435c1bf-88a0-43a5-80ff-00e3b6ef7427
-- title:
--   Automorphic: tensor Map std Vec
-- statement:
--   The Automorphic construction uses the tensor Map std Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L240-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L240-L247

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
variable [DecidableEq ι] (R : Type*) [CommRing R] [Algebra K R]
variable {κ : Type*} [Fintype κ] (b : Basis κ K E)
variable {R}
omit [Algebra.IsQuadraticExtension K E] [Fintype ι] [Fintype κ]

theorem GroundTheory.Automorphic.tensorMap_stdVec (a : ι × κ) :
    (fun i => tensorMap E (Algebra.ofId K R) (stdVec K b a i)) = stdVec R b a := by sorry
