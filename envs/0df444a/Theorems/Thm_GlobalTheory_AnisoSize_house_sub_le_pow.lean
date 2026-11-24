-- Prove2me | Theorems.Thm_GlobalTheory_AnisoSize_house_sub_le_pow
-- name    : GlobalTheory.AnisoSize.house_sub_le_pow
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T10:58:22.201355+00:00
-- url     : https://prove2.me/theorems/6eb270c2-6b7d-484f-a5d8-31724052d9ad
-- title:
--   Aniso Size: house sub le pow
-- statement:
--   The Aniso Size construction uses the house sub le pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/AnisotropicFiniteLengthsOfShortLatticeVector.lean#L183-L186

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {V : Type} [AddCommGroup V] [Module E V]
  {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ} {ν : V → ℝ} {B : ℝ}
omit [IsCMField E]

theorem GlobalTheory.AnisoSize.house_sub_le_pow {U : ℝ} (hU : 2 ≤ U) {a b : ℕ} {x y : E}
    (hx : house x ≤ U ^ a) (hy : house y ≤ U ^ b) : house (x - y) ≤ U ^ (max a b + 1) := by sorry
