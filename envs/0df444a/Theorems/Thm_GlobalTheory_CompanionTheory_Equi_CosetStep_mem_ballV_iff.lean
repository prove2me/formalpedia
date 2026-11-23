-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_mem_ballV_iff
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.mem_ballV_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:28:43.22268+00:00
-- url     : https://prove2.me/theorems/7f73ed3b-24cd-43a0-8ede-52d08c5926ee
-- title:
--   Coset Step: mem ball V iff
-- statement:
--   The Coset Step construction uses the mem ball V iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L97-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L97-L104

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.mem_ballV_iff (v : HeightOneSpectrum (𝓞 F)) (k : ℕ) (t : F) :
    algebraMap F (Fv F v) t ∈ ballV v k ↔ v.valuation F t ≤ WithZero.exp (-(k : ℤ)) := by sorry
