-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_isUnit_gram
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.isUnit_gram
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:59:09.0895+00:00
-- url     : https://prove2.me/theorems/23078b99-04df-48d5-b786-3b1798b7eeb5
-- title:
--   Eichler Transf: is Unit gram
-- statement:
--   The Eichler Transf construction uses the is Unit gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L24-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L24-L45

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ExtendByZeroApplyOfNe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.EichlerTransf
open scoped ComplexOrder
variable {n m : ℕ}

theorem GlobalTheory.CompanionTheory.EichlerTransf.isUnit_gram (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P) :
    IsUnit (aᴴ * a + (1 - P)) := by sorry
