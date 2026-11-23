-- Prove2me | Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_of_isLocalizedModule_maximal
-- name    : GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule_maximal
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:38:50.12439+00:00
-- url     : https://prove2.me/theorems/b5676a27-993b-4b57-8dcd-aac99e293fe8
-- title:
--   Is Quasi Regular Seq: of is Localized Module maximal
-- statement:
--   The Is Quasi Regular Seq construction uses the of is Localized Module maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L636-L654
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/IsQuasiRegularSeqSelfIffLocalizationMaximal.lean#L636-L654

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (S : Type*) [CommRing S] [Algebra R S]
variable {N : Type*} [AddCommGroup N] [Module R N]

theorem GlobalTheory.IsQuasiRegularSeq.of_isLocalizedModule_maximal {f : ι → R}
    (Mₚ : ∀ (P : Ideal R) [P.IsMaximal], Type*)
    [∀ (P : Ideal R) [P.IsMaximal], AddCommGroup (Mₚ P)]
    [∀ (P : Ideal R) [P.IsMaximal], Module R (Mₚ P)]
    (g : ∀ (P : Ideal R) [P.IsMaximal], M →ₗ[R] Mₚ P)
    [∀ (P : Ideal R) [P.IsMaximal], IsLocalizedModule P.primeCompl (g P)]
    (h : ∀ (P : Ideal R) [P.IsMaximal], Ideal.span (Set.range f) ≤ P →
      IsQuasiRegularSeq (Mₚ P) f) : IsQuasiRegularSeq M f := by sorry
