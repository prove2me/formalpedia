-- Prove2me | Theorems.Thm_GlobalTheory_sum_neg_one_pow_hdim_eq_add
-- name    : GlobalTheory.sum_neg_one_pow_hdim_eq_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:42:03.808093+00:00
-- url     : https://prove2.me/theorems/3465e50f-a7e2-4625-a00c-52f731bb4c29
-- title:
--   Global Theory: sum neg one pow hdim eq add
-- statement:
--   The Global Theory construction uses the sum neg one pow hdim eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L326-L331
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L326-L331

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
variable {X : Scheme.{u}}
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
include hS

theorem GlobalTheory.sum_neg_one_pow_hdim_eq_add (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i < N, Module.Finite k (coh S.X₃ i)) (hN : Subsingleton (coh S.X₁ N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₁ i +
        ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k S.X₃ i := by sorry
