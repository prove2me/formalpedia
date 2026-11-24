-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_hsNormSq_sub_hsTruncation
-- name    : GroundTheory.Automorphic.hsNormSq_sub_hsTruncation
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:35:42.016734+00:00
-- url     : https://prove2.me/theorems/2f7fee7a-06ea-476c-9d0a-ce12be4aa2f5
-- title:
--   Automorphic: hs Norm Sq sub hs Truncation
-- statement:
--   The Automorphic construction uses the hs Norm Sq sub hs Truncation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L56-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/HilbertSchmidtCompact.lean#L56-L66

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
omit [CompleteSpace K]

theorem GroundTheory.Automorphic.hsNormSq_sub_hsTruncation (T : H →L[𝕜] K) (F : Finset (exists_hilbertBasis 𝕜 H).choose) :
    hsNormSq (T - hsTruncation (stdHilbertBasis 𝕜 H) T F) =
      ∑' i : {i // i ∉ F}, ‖T (stdHilbertBasis 𝕜 H i)‖ₑ ^ 2 := by sorry
