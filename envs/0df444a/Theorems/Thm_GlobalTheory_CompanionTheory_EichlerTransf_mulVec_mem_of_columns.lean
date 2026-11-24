-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_EichlerTransf_mulVec_mem_of_columns
-- name    : GlobalTheory.CompanionTheory.EichlerTransf.mulVec_mem_of_columns
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:27.713742+00:00
-- url     : https://prove2.me/theorems/f2e01698-2d4c-43e3-9b28-55f2cb33ae4d
-- title:
--   Eichler Transf: mul Vec mem of columns
-- statement:
--   The Eichler Transf construction uses the mul Vec mem of columns property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L16-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ExtendByZeroApplyOfNe.lean#L16-L22

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

theorem GlobalTheory.CompanionTheory.EichlerTransf.mulVec_mem_of_columns {p q : ℕ} (G : Submodule ℂ (Fin p → ℂ))
    (M : Matrix (Fin p) (Fin q) ℂ) (h : ∀ i, (fun j => M j i) ∈ G) (z : Fin q → ℂ) :
    M *ᵥ z ∈ G := by sorry
