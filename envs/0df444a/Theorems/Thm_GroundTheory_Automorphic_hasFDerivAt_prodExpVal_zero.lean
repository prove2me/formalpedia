-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_prodExpVal_zero
-- name    : GroundTheory.Automorphic.hasFDerivAt_prodExpVal_zero
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:35.955803+00:00
-- url     : https://prove2.me/theorems/64184834-2212-4443-a904-50bd5ac582e1
-- title:
--   Automorphic: has FDeriv At prod Exp Val zero
-- statement:
--   The Automorphic construction uses the has FDeriv At prod Exp Val zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L38-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L38-L73

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinBasic
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinHaarCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped Manifold ContDiff Topology
open NormedSpace Set Filter
set_option linter.unusedSectionVars false
variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

theorem GroundTheory.Automorphic.hasFDerivAt_prodExpVal_zero {d : ℕ} (X : Fin d → 𝔸) :
    HasFDerivAt (prodExpVal X)
      (∑ i, (ContinuousLinearMap.proj i : (Fin d → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by sorry
