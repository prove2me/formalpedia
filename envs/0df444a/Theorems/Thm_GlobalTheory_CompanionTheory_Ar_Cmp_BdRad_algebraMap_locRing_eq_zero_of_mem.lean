-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_algebraMap_locRing_eq_zero_of_mem
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.algebraMap_locRing_eq_zero_of_mem
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:27:10.521434+00:00
-- url     : https://prove2.me/theorems/cbf0077d-685e-59a6-a486-b83ae2d9eead
-- title:
--   Bd Rad: algebra Map loc Ring eq zero of mem
-- statement:
--   The Bd Rad construction uses the algebra Map loc Ring eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L18-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L18-L23

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_ChPrime
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_RegDom
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_JacChart
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_RegularSystemOfParametersLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.BdRad
open MvPolynomial ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
variable {m : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.algebraMap_locRing_eq_zero_of_mem (I : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ)
    {a : MvPolynomial (Fin m) ℂ} (ha : a ∈ I) : algebraMap _ (locRing I t) a = 0 := by sorry
