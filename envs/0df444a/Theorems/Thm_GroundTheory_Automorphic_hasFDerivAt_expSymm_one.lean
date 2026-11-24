-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hasFDerivAt_expSymm_one
-- name    : GroundTheory.Automorphic.hasFDerivAt_expSymm_one
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:35:47.102177+00:00
-- url     : https://prove2.me/theorems/bda3f6b8-19fe-4c86-89cd-9c773ca51672
-- title:
--   Automorphic: has FDeriv At exp Symm one
-- statement:
--   The Automorphic construction uses the has FDeriv At exp Symm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L75-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/DixmierMalliavinHaarCoord.lean#L75-L83

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

theorem GroundTheory.Automorphic.hasFDerivAt_expSymm_one :
    HasFDerivAt (expPartialHomeomorph ℝ 𝔸).symm (1 : 𝔸 →L[ℝ] 𝔸) 1 := by sorry
