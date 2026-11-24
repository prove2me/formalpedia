-- Prove2me | Theorems.Thm_GlobalTheory_NormChar_split_trivial
-- name    : GlobalTheory.NormChar.split_trivial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:37:27.437355+00:00
-- url     : https://prove2.me/theorems/25958ca7-613e-4eba-814c-c3c0b1341480
-- title:
--   Norm Char: split trivial
-- statement:
--   The Norm Char construction uses the split trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeNormCyclotomicCharNeOne.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsPrimeNormCyclotomicCharNeOne.lean#L11-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEqStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NcardPrimesOverEqFinrankOfTrivialFrobeniusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsPrimeNormCyclotomicCharNeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open GlobalTheory GlobalTheory.NormChar

theorem GlobalTheory.NormChar.split_trivial (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] [IsGalois K M]
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (h : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∀ P ∈ v.asIdeal.primesOver (𝓞 M), ∀ x : 𝓞 M,
      x ^ Ideal.absNorm v.asIdeal - x ∈ P) : Module.finrank K M = 1 := by sorry
