-- Prove2me | Theorems.Thm_GlobalTheory_cohOn_sum_neg_one_pow_finrank
-- name    : GlobalTheory.cohOn.sum_neg_one_pow_finrank
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:42.591284+00:00
-- url     : https://prove2.me/theorems/c2ee2c94-2fe2-44be-bf25-c2c8052c3ab2
-- title:
--   coh On: sum neg one pow finrank
-- statement:
--   The coh On construction uses the sum neg one pow finrank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L276-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L276-L285

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
open GlobalTheory.cohOn
variable (R : Type v) [CommRing R] [Algebra R Γ(X, ⊤)]
  {S : ShortComplex X.Modules} (hS : S.ShortExact)
variable (U : X.Opens) (n : ℕ)
include hS
variable (k : Type v) [Field k] [Algebra k Γ(X, ⊤)]

theorem GlobalTheory.cohOn.sum_neg_one_pow_finrank (N : ℕ) (h₁ : ∀ i < N, Module.Finite k (cohOn S.X₁ U i))
    (h₂ : ∀ i < N, Module.Finite k (cohOn S.X₂ U i))
    (h₃ : ∀ i < N, Module.Finite k (cohOn S.X₃ U i)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (finrank k (cohOn S.X₁ U i) -
        finrank k (cohOn S.X₂ U i) + finrank k (cohOn S.X₃ U i)) =
      -(-1) ^ N * finrank k (LinearMap.ker (map k S.f U N)) := by sorry
