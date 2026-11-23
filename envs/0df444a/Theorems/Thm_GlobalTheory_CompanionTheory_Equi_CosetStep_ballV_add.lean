-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Equi_CosetStep_ballV_add
-- name    : GlobalTheory.CompanionTheory.Equi.CosetStep.ballV_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:27:56.895975+00:00
-- url     : https://prove2.me/theorems/1cfc15b3-da53-4d0a-a32d-b80062f28f1f
-- title:
--   Coset Step: ball V add
-- statement:
--   The Coset Step construction uses the ball V add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L106-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CosetCongruenceRefinement.lean#L106-L109

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

theorem GlobalTheory.CompanionTheory.Equi.CosetStep.ballV_add {v : HeightOneSpectrum (𝓞 F)} {k : ℕ} {a b : Fv F v}
    (ha : a ∈ ballV v k) (hb : b ∈ ballV v k) : a + b ∈ ballV v k := by sorry
