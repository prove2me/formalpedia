-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_exists_gram_inverse
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.exists_gram_inverse
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:49.369664+00:00
-- url     : https://prove2.me/theorems/68677240-f639-43cd-b386-7ad3997d05c0
-- title:
--   Eichler Transf: exists gram inverse
-- statement:
--   The Eichler Transf construction uses the exists gram inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L47-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L47-L76

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

theorem GlobalTheory.CompanionTheory.EichlerTransf.exists_gram_inverse (a : Matrix (Fin n) (Fin m) ℂ) (b : Matrix (Fin m) (Fin n) ℂ)
    (P : Matrix (Fin m) (Fin m) ℂ) (hPh : Pᴴ = P) (hPP : P * P = P) (hb : b * a = P)
    (hap : a * P = a) :
    ∃ C H : Matrix (Fin m) (Fin m) ℂ, C * H = P ∧ aᴴ * a * C = P ∧ C * P = C := by sorry
