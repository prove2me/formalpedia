-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_mul_le_pow
-- name    : GlobalTheory.AnisoSize.mul_le_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:33.492917+00:00
-- url     : https://prove2.me/theorems/7112dc0f-5809-4041-9bfd-88bc689a8d29
-- title:
--   Aniso Size: mul le pow
-- statement:
--   The Aniso Size construction uses the mul le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L135-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L135-L138

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize

theorem GlobalTheory.AnisoSize.mul_le_pow {U x y : ℝ} {a b : ℕ} (hU : 2 ≤ U) (hx : x ≤ U ^ a) (hy : y ≤ U ^ b)
    (h0 : 0 ≤ y) : x * y ≤ U ^ (a + b) := by sorry
