-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_MinHom_isMultiHomogIdeal_of_mem_minimalPrimes_sup
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T14:18:13.914857+00:00
-- url     : https://prove2.me/theorems/75d701cb-2b6a-5629-b768-893483fc191e
-- title:
--   Min Hom: is Multi Homog Ideal of mem minimal Primes sup
-- statement:
--   The Min Hom construction uses the is Multi Homog Ideal of mem minimal Primes sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MinimalPrimesOfMultihomogSup.lean#L14-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/MinimalPrimesOfMultihomogSup.lean#L14-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_MinimalPrimesOfMultihomogSup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.MinHom
open MvPolynomial ReciprocityTheory.AnForm.R
attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem GlobalTheory.CompanionTheory.Ar.Cmp.MinHom.isMultiHomogIdeal_of_mem_minimalPrimes_sup :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)),
      IsMultiHomogIdeal P → IsMultiHomogIdeal D →
        ∀ Q ∈ (P ⊔ D).minimalPrimes, IsMultiHomogIdeal Q := by sorry
