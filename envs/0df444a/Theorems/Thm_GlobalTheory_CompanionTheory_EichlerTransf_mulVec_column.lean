-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_mulVec_column
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.mulVec_column
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:01:22.200796+00:00
-- url     : https://prove2.me/theorems/bad69d29-9fd6-4576-aac7-e7df6c0b77a1
-- title:
--   Eichler Transf: mul Vec column
-- statement:
--   The Eichler Transf construction uses the mul Vec column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L12-L14

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

theorem GlobalTheory.CompanionTheory.EichlerTransf.mulVec_column {p q r : ℕ} (N : Matrix (Fin p) (Fin q) ℂ) (M : Matrix (Fin q) (Fin r) ℂ)
    (i : Fin r) : (N *ᵥ fun j => M j i) = fun j => (N * M) j i := by sorry
