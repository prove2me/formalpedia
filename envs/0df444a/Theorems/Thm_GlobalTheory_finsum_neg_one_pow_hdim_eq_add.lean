-- Prove2me | Theorems.Thm_GlobalTheory_finsum_neg_one_pow_hdim_eq_add
-- name    : GlobalTheory.finsum_neg_one_pow_hdim_eq_add
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:10.65401+00:00
-- url     : https://prove2.me/theorems/1bc61695-957e-44ee-a9e9-d5c7baafdc85
-- title:
--   Global Theory: finsum neg one pow hdim eq add
-- statement:
--   The Global Theory construction uses the finsum neg one pow hdim eq add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L343-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L343-L356

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

theorem GlobalTheory.finsum_neg_one_pow_hdim_eq_add (h₁ : ∀ i, Module.Finite k (coh S.X₁ i))
    (h₃ : ∀ i, Module.Finite k (coh S.X₃ i))
    (hv₁ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₁ i))
    (hv₃ : ∃ N, ∀ i, N ≤ i → Subsingleton (coh S.X₃ i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₂ i =
      ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₁ i + ∑ᶠ i, (-1 : ℤ) ^ i * hdim k S.X₃ i := by sorry
