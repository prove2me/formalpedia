-- Prove2me | Theorems.Thm_GlobalTheory_Mem_PartialZeta_hasSum_cnt
-- name    : GlobalTheory.Mem.PartialZeta.hasSum_cnt
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:23:03.32966+00:00
-- url     : https://prove2.me/theorems/34ce4b42-b195-40c2-95ae-629f95087398
-- title:
--   Partial Zeta: has Sum cnt
-- statement:
--   The Partial Zeta construction uses the has Sum cnt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L273-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayClassPartialZetaContinuation.lean#L273-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeEpsteinZetaContinuationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayClassPartialZetaContinuation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.PartialZeta
variable {K : Type} [Field K] [NumberField K]

theorem GlobalTheory.Mem.PartialZeta.hasSum_cnt {M : ℕ} (hM : Ideal.span {(M : 𝓞 K)} ≠ ⊤) (D : RayData K M) (c : D.G) (s a : ℂ)
    (h : HasSum (fun I : {I : Ideal (𝓞 K) // IsCoprime I (Ideal.span {(M : 𝓞 K)}) ∧ D.cls I = c} =>
      (Ideal.absNorm I.1 : ℂ) ^ (-s)) a) : LSeriesHasSum (D.cnt c) s a := by sorry
