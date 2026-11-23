-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_pow_mul
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.exists_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:56.416692+00:00
-- url     : https://prove2.me/theorems/d623f5a3-5e62-48dd-9c76-c96ec0477cee
-- title:
--   Coset Step: exists pow mul
-- statement:
--   The Coset Step construction uses the exists pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L13-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L13-L38

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.exists_pow_mul (v : HeightOneSpectrum (𝓞 F)) {D : Ideal (𝓞 F)} (hD : D ≠ ⊥) :
    ∃ (m : ℕ) (B : Ideal (𝓞 F)), D = v.asIdeal ^ m * B ∧ ¬ B ≤ v.asIdeal := by sorry
