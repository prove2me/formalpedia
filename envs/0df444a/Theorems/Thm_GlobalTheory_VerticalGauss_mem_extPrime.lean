-- Prove2me | Theorems.Thm_GlobalTheory_VerticalGauss_mem_extPrime
-- name    : GlobalTheory.VerticalGauss.mem_extPrime
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:07.163648+00:00
-- url     : https://prove2.me/theorems/e4759a02-cc4d-4444-a91e-0eeda1359940
-- title:
--   Vertical Gauss: mem ext Prime
-- statement:
--   The Vertical Gauss construction uses the mem ext Prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/FiniteVerticalGaussValuations.lean#L20-L23

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.VerticalGauss
open IsLocalRing IsDedekindDomain

theorem GlobalTheory.VerticalGauss.mem_extPrime {K : Type} [Field K] [NumberField K] {σ : Type}
    (la : HeightOneSpectrum (𝓞 K)) (p : MvPolynomial σ (𝓞 K)) :
    p ∈ extPrime σ la ↔ ∀ m, p.coeff m ∈ la.asIdeal := by sorry
