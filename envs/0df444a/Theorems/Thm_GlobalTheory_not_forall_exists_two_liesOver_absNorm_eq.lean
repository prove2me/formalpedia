-- Prove2me | Theorems.Thm_GlobalTheory_not_forall_exists_two_liesOver_absNorm_eq
-- name    : GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:12:59.619446+00:00
-- url     : https://prove2.me/theorems/6d7cc8a5-ab9a-4536-b6eb-926dd66799cd
-- title:
--   Global Theory: not forall exists two lies Over abs Norm eq
-- statement:
--   The Global Theory construction uses the not forall exists two lies Over abs Norm eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotForallExistsTwoLiesOverAbsNormEq.lean#L13-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NotForallExistsTwoLiesOverAbsNormEq.lean#L13-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NumberFieldPrimeZetaSumAddLogIsBigO
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotForallExistsTwoLiesOverAbsNormEq
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
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem GlobalTheory.not_forall_exists_two_liesOver_absNorm_eq :
    ∀ (K M : Type) [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M] (S : Set (HeightOneSpectrum (𝓞 K))), S.Finite → ¬ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S → ∃ P P' : HeightOneSpectrum (𝓞 M), P ≠ P' ∧ P.asIdeal.LiesOver v.asIdeal ∧ P'.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm P'.asIdeal = Ideal.absNorm v.asIdeal := by sorry
