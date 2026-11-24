-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_locMem_neg
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_neg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:05.968234+00:00
-- url     : https://prove2.me/theorems/68b7467a-3c58-4cd3-abea-61a0fc7b89f2
-- title:
--   Coset Step: loc Mem neg
-- statement:
--   The Coset Step construction uses the loc Mem neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L57-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L57-L62

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.locMem_neg {I : Ideal (𝓞 F)} {w : HeightOneSpectrum (𝓞 F)} {a : F}
    (ha : LocMem I w a) : LocMem I w (-a) := by sorry
