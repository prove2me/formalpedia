-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_map_mem_pow_smul_top_iff
-- name    : GlobalTheory.IsQuasiRegularSeq.map_mem_pow_smul_top_iff
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:39.190541+00:00
-- url     : https://prove2.me/theorems/032e0a22-e25c-4ec7-86ca-954890ffa412
-- title:
--   Is Quasi Regular Seq: map mem pow smul top iff
-- statement:
--   The Is Quasi Regular Seq construction uses the map mem pow smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSMulRegularQuotIffMemNonZeroDivisors.lean#L47-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSMulRegularQuotIffMemNonZeroDivisors.lean#L47-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSMulRegularQuotIffMemNonZeroDivisors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
  {f : ι → R}

theorem GlobalTheory.IsQuasiRegularSeq.map_mem_pow_smul_top_iff (h : IsQuasiRegularSeq M f) (T : Submonoid R)
    (hT : ∀ t ∈ T, IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) t)
    {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) [IsLocalizedModule T g] (a : ℕ)
    (m : M) : g m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R N) ↔
      m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by sorry
