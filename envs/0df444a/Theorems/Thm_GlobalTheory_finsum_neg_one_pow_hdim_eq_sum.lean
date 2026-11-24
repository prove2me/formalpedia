-- Prove2me | Theorems.Thm_GlobalTheory_finsum_neg_one_pow_hdim_eq_sum
-- name    : GlobalTheory.finsum_neg_one_pow_hdim_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T21:39:54.828836+00:00
-- url     : https://prove2.me/theorems/af3358a1-fb26-4dbb-bf30-6c591a202da3
-- title:
--   Global Theory: finsum neg one pow hdim eq sum
-- statement:
--   The Global Theory construction uses the finsum neg one pow hdim eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L335-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L335-L341

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
omit hS

theorem GlobalTheory.finsum_neg_one_pow_hdim_eq_sum (F : X.Modules) (N : ℕ)
    (hN : ∀ i, N ≤ i → Subsingleton (coh F i)) :
    ∑ᶠ i, (-1 : ℤ) ^ i * hdim k F i = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * hdim k F i := by sorry
