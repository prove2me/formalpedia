-- Prove2me | Theorems.Thm_GlobalTheory_SmoothForms_Short_size_sum_le
-- name    : GlobalTheory.SmoothForms.Short.size_sum_le
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:21:01.600616+00:00
-- url     : https://prove2.me/theorems/cad58fd6-13e4-48d0-8ef5-5250f26c62f4
-- title:
--   Short: size sum le
-- statement:
--   The Short construction uses the size sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L136-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ShortLatticeVectorBoundedSizeOfOrthogonalFrame.lean#L136-L147

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ShortLatticeVectorBoundedSizeOfOrthogonalFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms GlobalTheory.HermClass Module Submodule NumberField Matrix
open GlobalTheory GlobalTheory.SmoothForms GlobalTheory.SmoothForms.Short

theorem GlobalTheory.SmoothForms.Short.size_sum_le {E : Type} [Field E] [NumberField E] [IsCMField E]
    {V : Type} [AddCommGroup V] [Module E V] {h : V →ₗ[E] V →ₗ⋆[E] E} {Λ : Submodule ℤ V} {N : ℤ}
    {ν : V → ℝ} {B : ℝ} (H : Sized h Λ N ν B) {ι : Type} (s : Finset ι) (f : ι → V) :
    ν (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ν (f i) := by sorry
