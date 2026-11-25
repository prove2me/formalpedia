-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_isCompactOperator_hsTruncation
-- name    : GroundTheory.Automorphic.isCompactOperator_hsTruncation
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:24.637013+00:00
-- url     : https://prove2.me/theorems/b084057b-2ce9-40ef-aedf-5e746d1543a7
-- title:
--   Automorphic: is Compact Operator hs Truncation
-- statement:
--   The Automorphic construction uses the is Compact Operator hs Truncation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L34-L42

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

theorem GroundTheory.Automorphic.isCompactOperator_hsTruncation {ι : Type*} (b : HilbertBasis ι 𝕜 H) (T : H →L[𝕜] K)
    (F : Finset ι) : IsCompactOperator (hsTruncation b T F) := by sorry
