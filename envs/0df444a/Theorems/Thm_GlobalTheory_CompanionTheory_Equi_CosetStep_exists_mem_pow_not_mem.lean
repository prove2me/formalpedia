-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_exists_mem_pow_not_mem
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.exists_mem_pow_not_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:26.682933+00:00
-- url     : https://prove2.me/theorems/37855a33-3fb5-4d25-bebe-2f79016b489b
-- title:
--   Coset Step: exists mem pow not mem
-- statement:
--   The Coset Step construction uses the exists mem pow not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L40-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L40-L46

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.exists_mem_pow_not_mem {v w : HeightOneSpectrum (𝓞 F)} (hw : w ≠ v) (k : ℕ) :
    ∃ e ∈ v.asIdeal ^ k, e ∉ w.asIdeal := by sorry
