-- Prove2me | Theorems.Thm_GlobalTheory_NormCharL_sup_eq_top_iff
-- name    : GlobalTheory.NormCharL.sup_eq_top_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:35:39.776809+00:00
-- url     : https://prove2.me/theorems/f4061643-4659-4661-9dc8-8156189ab854
-- title:
--   Norm Char L: sup eq top iff
-- statement:
--   The Norm Char L construction uses the sup eq top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsContinuousNormCharLFunctionNeZeroOne.lean#L25-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsContinuousNormCharLFunctionNeZeroOne.lean#L25-L54

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMixedSpaceNormSignCharacterStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsContinuousNormCharLFunctionNeZeroOne
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
open GlobalTheory.NormCharL

theorem GlobalTheory.NormCharL.sup_eq_top_iff (K : Type) [Field K] [NumberField K] (m : ℕ) (hm : m.Prime)
    (I : Ideal (𝓞 K)) : I ⊔ Ideal.span {(m : 𝓞 K)} = ⊤ ↔ ¬ m ∣ Ideal.absNorm I := by sorry
