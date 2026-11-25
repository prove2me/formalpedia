-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Par_chPrime_le_of_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.chPrime_le_of_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:36.848365+00:00
-- url     : https://prove2.me/theorems/64185f7d-3789-4e43-8132-0c4eab1051bd
-- title:
--   Par: ch Prime le of mem
-- statement:
--   The Par construction uses the ch Prime le of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L47-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/PrimesBelowParams.lean#L47-L64

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_PrimesBelowParams
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages GlobalTheory.CompanionTheory.Ar.Cmp
variable {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Par.chPrime_le_of_mem {I 𝔮 : Ideal (MvPolynomial (Fin m) ℂ)} {t : Fin m → ℂ}
    {f : MvPolynomial (Fin m) ℂ} (h𝔮 : 𝔮.IsPrime) (hI𝔮 : I ≤ 𝔮) (h𝔮t : 𝔮 ≤ ptIdeal t)
    (hf : f ∈ 𝔮) : chPrime I t f ≤ 𝔮 := by sorry
