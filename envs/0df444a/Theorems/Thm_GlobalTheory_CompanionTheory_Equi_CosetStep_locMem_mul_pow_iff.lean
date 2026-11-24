-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_mul_pow_iff
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_mul_pow_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:37:18.79712+00:00
-- url     : https://prove2.me/theorems/0466c3e5-2842-43d1-a94a-ba9fc7147fdf
-- title:
--   Coset Step: loc Mem mul pow iff
-- statement:
--   The Coset Step construction uses the loc Mem mul pow iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L68-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L68-L78

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetOff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CosetCongruenceRefinement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Equi GlobalTheory.CompanionTheory.Equi.CosetStep
variable {F : Type} [Field F] [NumberField F]

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_mul_pow_iff {I : Ideal (𝓞 F)} {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ)
    {t : F} : LocMem (I * v.asIdeal ^ k) w t ↔ LocMem I w t := by sorry
