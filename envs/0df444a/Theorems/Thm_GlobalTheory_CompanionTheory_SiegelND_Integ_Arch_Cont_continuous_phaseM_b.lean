-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_Cont_continuous_phaseM_b
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont.continuous_phaseM_b
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:14:10.166268+00:00
-- url     : https://prove2.me/theorems/ef5a2a9f-b628-495b-b5d5-804e1bf7cf99
-- title:
--   Cont: continuous phase M b
-- statement:
--   The Cont construction uses the continuous phase M b property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanOrbitalIntegralContinuous.lean#L22-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanOrbitalIntegralContinuous.lean#L22-L35

import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanOrbitalIntegralContinuous
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.Cont.continuous_phaseM_b {W : Type} [Fintype W] {n M : ℕ}
    (J : W → Matrix (Fin M) (Fin M) ℂ) (X : W → Fin n → Fin M → ℂ) :
    Continuous fun b : W → hermC n =>
      phaseM J (fun w => (b w : Matrix (Fin n) (Fin n) ℂ)) X := by sorry
