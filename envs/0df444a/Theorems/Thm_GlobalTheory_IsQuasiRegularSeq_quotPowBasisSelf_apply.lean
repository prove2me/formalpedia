-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_quotPowBasisSelf_apply
-- name    : GlobalTheory.IsQuasiRegularSeq.quotPowBasisSelf_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:11:20.986118+00:00
-- url     : https://prove2.me/theorems/80423b1c-31a0-4f8d-8b56-f9fe3193be69
-- title:
--   Is Quasi Regular Seq: quot Pow Basis Self apply
-- statement:
--   The Is Quasi Regular Seq construction uses the quot Pow Basis Self apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSMulRegularQuotIffMemNonZeroDivisors.lean#L378-L383
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsSMulRegularQuotIffMemNonZeroDivisors.lean#L378-L383

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {f : ι → R}
  {A : Type*} [CommRing A] [Algebra A R]

theorem GlobalTheory.IsQuasiRegularSeq.quotPowBasisSelf_apply (h : IsQuasiRegularSeq R f)
    {κ : Type*} (b : Module.Basis κ A (R ⧸ Ideal.span (Set.range f)))
    (r : κ → R) (hr : ∀ j, Ideal.Quotient.mk _ (r j) = b j) (k : ℕ) (p : MonoDegLE ι k × κ) :
    h.quotPowBasisSelf b r hr k p = Ideal.Quotient.mk _ (monoVal f p.1.1 * r p.2) := by sorry
