-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompactOperator_innerSL_smulRight
-- name    : GroundTheory.Automorphic.isCompactOperator_innerSL_smulRight
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:36:05.27521+00:00
-- url     : https://prove2.me/theorems/5eed3092-e2fc-4904-9c5a-73c6a013b4be
-- title:
--   Automorphic: is Compact Operator inner SL smul Right
-- statement:
--   The Automorphic construction uses the is Compact Operator inner SL smul Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L17-L27

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
omit [CompleteSpace H] [CompleteSpace K]

theorem GroundTheory.Automorphic.isCompactOperator_innerSL_smulRight (e : H) (y : K) :
    IsCompactOperator ((innerSL 𝕜 e).smulRight y) := by sorry
