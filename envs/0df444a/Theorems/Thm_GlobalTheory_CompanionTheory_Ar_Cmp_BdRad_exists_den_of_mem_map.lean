-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_BdRad_exists_den_of_mem_map
-- name    : GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_of_mem_map
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:06.391688+00:00
-- url     : https://prove2.me/theorems/d5c3a029-c233-4053-953f-ffde55ddff53
-- title:
--   Bd Rad: exists den of mem map
-- statement:
--   The Bd Rad construction uses the exists den of mem map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L49-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/MetricProofs/RegularSystemOfParametersLocalRing.lean#L49-L78

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

theorem GlobalTheory.CompanionTheory.Ar.Cmp.BdRad.exists_den_of_mem_map (I D : Ideal (MvPolynomial (Fin m) ℂ)) (t : Fin m → ℂ) (hID : I ≤ D)
    (hp : ∀ h ∈ I, eval t h = 0) {f : MvPolynomial (Fin m) ℂ}
    (hf : algebraMap _ (locRing I t) f ∈ Ideal.map (algebraMap _ (locRing I t)) D) :
    ∃ s, eval t s ≠ 0 ∧ s * f ∈ D := by sorry
