-- Prove2me | Theorems.Thm_GlobalTheory_NormSign_sgn_mul
-- name    : GlobalTheory.NormSign.sgn_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:37:36.241843+00:00
-- url     : https://prove2.me/theorems/b481768c-909d-43d5-bf22-04054bbd2a82
-- title:
--   Norm Sign: sgn mul
-- statement:
--   The Norm Sign construction uses the sgn mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMixedSpaceNormSignCharacter.lean#L81-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMixedSpaceNormSignCharacter.lean#L81-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacter
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
open GlobalTheory GlobalTheory.NormSign
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical
open NumberField.InfinitePlace
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.NormSign.sgn_mul {ε : ℂ} (hε : ε * ε = 1) (a b : ℝ) :
    _root_.GlobalTheory.NormSign.sgn ε (a * b) = _root_.GlobalTheory.NormSign.sgn ε a * _root_.GlobalTheory.NormSign.sgn ε b := by sorry
