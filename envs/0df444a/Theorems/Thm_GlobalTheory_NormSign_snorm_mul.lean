-- Prove2me | Theorems.Thm_GlobalTheory_NormSign_snorm_mul
-- name    : GlobalTheory.NormSign.snorm_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:36:15.705013+00:00
-- url     : https://prove2.me/theorems/a0c23dd2-a3e0-42f6-a43d-f4eb4bed636f
-- title:
--   Norm Sign: snorm mul
-- statement:
--   The Norm Sign construction uses the snorm mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMixedSpaceNormSignCharacter.lean#L20-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsMixedSpaceNormSignCharacter.lean#L20-L25

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

theorem GlobalTheory.NormSign.snorm_mul {K : Type} [Field K] [NumberField K]
    (x y : NumberField.mixedEmbedding.mixedSpace K) :
    _root_.GlobalTheory.NormSign.snorm (x * y) = _root_.GlobalTheory.NormSign.snorm x * _root_.GlobalTheory.NormSign.snorm y := by sorry
