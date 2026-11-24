-- Prove2me | Theorems.Thm_GlobalTheory_EisBL_NilAlg_tau_tau
-- name    : GlobalTheory.EisBL.NilAlg.tau_tau
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:06:04.849363+00:00
-- url     : https://prove2.me/theorems/ae3743f3-b642-4604-bf5f-77cd8485b27e
-- title:
--   Nil Alg: tau tau
-- statement:
--   The Nil Alg construction uses the tau tau property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L81-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/AutomorphicKernels/EisensteinSeriesG2/G2HaarMeasure/PhiEqZeroIff.lean#L81-L93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_EisensteinSeriesG2_G2HaarMeasure_PhiEqZeroIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open GlobalTheory GlobalTheory.EisBL GlobalTheory.EisBL.NilAlg
variable {B : Type} [CommRing B] {n : Type} [Fintype n] [DecidableEq n]

theorem GlobalTheory.EisBL.NilAlg.tau_tau (c : B →+* B) (hc : ∀ x, c (c x) = x) {J K : Matrix n n B} (ε : B) (hε : ε * ε = 1)
    (hJc : (J.map c)ᵀ = ε • J) (hKc : (K.map c)ᵀ = ε • K) (hJK : J * K = 1) (X : Matrix n n B) :
    tau c J K (tau c J K X) = X := by sorry
