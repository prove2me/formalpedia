-- Prove2me | Theorems.Thm_GlobalTheory_ChebCyc_primeSum_add_log_isBigO
-- name    : GlobalTheory.ChebCyc.primeSum_add_log_isBigO
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:11:36.246988+00:00
-- url     : https://prove2.me/theorems/fc0fa385-cd01-4d52-889f-bae6cba56222
-- title:
--   Cheb Cyc: prime Sum add log is Big O
-- statement:
--   The Cheb Cyc construction uses the prime Sum add log is Big O property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NumberFieldPrimeZetaSumAddLogIsBigO.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NumberFieldPrimeZetaSumAddLogIsBigO.lean#L63-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdealCharacterLContinuationNeZeroOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InfinitelyManyPrimesInRayClass
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NotInjectiveTwoPrimesEqualNormCofinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NumberFieldPrimeZetaSumAddLogIsBigO
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
open GlobalTheory GlobalTheory.ChebCyc
open NumberField IsDedekindDomain NumberField.mixedEmbedding Filter Topology Asymptotics Polynomial
open scoped ContDiff Classical

theorem GlobalTheory.ChebCyc.primeSum_add_log_isBigO : ∀ (K : Type) [Field K] [NumberField K], (fun s : ℝ => (∑' P : HeightOneSpectrum (𝓞 K), ((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ)) := by sorry
