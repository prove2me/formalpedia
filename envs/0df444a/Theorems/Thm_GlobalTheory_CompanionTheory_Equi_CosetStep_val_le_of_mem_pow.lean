-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_val_le_of_mem_pow
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.val_le_of_mem_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:16.899351+00:00
-- url     : https://prove2.me/theorems/88231349-398c-4e51-92d6-10e6ecddf445
-- title:
--   Coset Step: val le of mem pow
-- statement:
--   The Coset Step construction uses the val le of mem pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L80-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L80-L84

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.val_le_of_mem_pow (v : HeightOneSpectrum (𝓞 F)) {y : 𝓞 F} {k : ℕ}
    (hy : y ∈ v.asIdeal ^ k) :
    v.valuation F (algebraMap (𝓞 F) F y) ≤ WithZero.exp (-(k : ℤ)) := by sorry
