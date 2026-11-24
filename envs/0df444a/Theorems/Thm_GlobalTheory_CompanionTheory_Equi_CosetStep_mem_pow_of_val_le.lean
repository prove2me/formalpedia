-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_mem_pow_of_val_le
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.mem_pow_of_val_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:38:32.840127+00:00
-- url     : https://prove2.me/theorems/33b770b0-3261-4a3a-8c2e-c3b3deac59c2
-- title:
--   Coset Step: mem pow of val le
-- statement:
--   The Coset Step construction uses the mem pow of val le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L86-L90

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.mem_pow_of_val_le (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ))) :
    y ∈ v.asIdeal ^ k := by sorry
