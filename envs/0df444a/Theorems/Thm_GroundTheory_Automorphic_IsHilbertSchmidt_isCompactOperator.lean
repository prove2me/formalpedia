-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_isCompactOperator
-- name    : GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:31:28.205367+00:00
-- url     : https://prove2.me/theorems/a6a22801-9c5d-4a9e-96ef-d868429186ba
-- title:
--   Is Hilbert Schmidt: is Compact Operator
-- statement:
--   The Is Hilbert Schmidt construction uses the is Compact Operator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L68-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L68-L88

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

theorem GroundTheory.Automorphic.IsHilbertSchmidt.isCompactOperator {T : H →L[𝕜] K} (hT : IsHilbertSchmidt T) :
    IsCompactOperator T := by sorry
