-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_KillSum_add_killed
-- name    : GlobalTheory.CompanionTheory.KillSum.add_killed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T11:50:56.504845+00:00
-- url     : https://prove2.me/theorems/525abe80-9985-4a09-9f26-28a1a7fd956b
-- title:
--   Kill Sum: add killed
-- statement:
--   The Kill Sum construction uses the add killed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilator.lean#L16-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/TensorSumAnnihilator.lean#L16-L36

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_TensorSumAnnihilator
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.KillSum

theorem GlobalTheory.CompanionTheory.KillSum.add_killed {R : Type*} [CommRing R] [Algebra ℂ R] (x y : R) (P Q : Multiset ℂ)
    (hP : (P.map fun c => x - algebraMap ℂ R c).prod = 0)
    (hQ : (Q.map fun c => y - algebraMap ℂ R c).prod = 0) :
    ((Q.bind fun b => P.map fun a => a + b).map fun c => (x + y) - algebraMap ℂ R c).prod = 0 := by sorry
