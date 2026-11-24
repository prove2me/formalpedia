-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_eichler_isometry
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.eichler_isometry
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:58:03.451813+00:00
-- url     : https://prove2.me/theorems/e484e03c-1796-4a0c-a0cc-ddf23886531b
-- title:
--   Eichler Transf: eichler isometry
-- statement:
--   The Eichler Transf construction uses the eichler isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L78-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L78-L110

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

theorem GlobalTheory.CompanionTheory.EichlerTransf.eichler_isometry (J : Matrix (Fin n) (Fin n) ℂ) (a d : Matrix (Fin n) (Fin m) ℂ)
    (F : Matrix (Fin m) (Fin m) ℂ) (hJh : Jᴴ = J) (h1 : aᴴ * J * a = 0) (h2 : aᴴ * J * d = 0)
    (hF : F + Fᴴ = dᴴ * J * d) :
    (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J))ᴴ * J *
      (1 + a * (-(dᴴ * J) - F * (aᴴ * J)) + d * (aᴴ * J)) = J := by sorry
