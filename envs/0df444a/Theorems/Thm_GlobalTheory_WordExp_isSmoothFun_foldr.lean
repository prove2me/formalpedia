-- Prove2me | Theorems.Thm_GlobalTheory_WordExp_isSmoothFun_foldr
-- name    : GlobalTheory.WordExp.isSmoothFun_foldr
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:48:40.830217+00:00
-- url     : https://prove2.me/theorems/32270373-22e7-4f5b-9f84-f1a63f8997f1
-- title:
--   Word Exp: is Smooth Fun foldr
-- statement:
--   The Word Exp construction uses the is Smooth Fun foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightDerivWordExpCoordsDifferentialOperator.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/RightDerivWordExpCoordsDifferentialOperator.lean#L12-L16

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZeroMemSolSet
import Definitions.Def_Formalism_UnipotentAdelicQuotients_EllRegCheck
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoefVFContDiffOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RightDerivWordExpCoordsDifferentialOperator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ZetaZeros.D.EllReg GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.WordExp

theorem GlobalTheory.WordExp.isSmoothFun_foldr {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]
    [FiniteDimensional ℝ 𝔸] {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
    {f : G → ℂ} (hf : h.IsSmoothFun f) : ∀ l : List 𝔤, h.IsSmoothFun (l.foldr h.rightDeriv f)
  := by sorry
