-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_tensorMap_hermPair
-- name    : GroundTheory.Automorphic.tensorMap_hermPair
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:35:46.312026+00:00
-- url     : https://prove2.me/theorems/a99852d0-45ec-42d6-ae28-cf225f54c752
-- title:
--   Automorphic: tensor Map herm Pair
-- statement:
--   The Automorphic construction uses the tensor Map herm Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L179-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DefiniteClassNumber/HermTraceSelfOfHermValue.lean#L179-L198

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

theorem GroundTheory.Automorphic.tensorMap_hermPair {S : Type*} [CommRing S] [Algebra K S] (f : R →ₐ[K] S)
    (x y : ι → R ⊗[K] E) :
    tensorMap E f (hermPair K H R x y) =
      hermPair K H S (fun i => tensorMap E f (x i)) (fun i => tensorMap E f (y i)) := by sorry
