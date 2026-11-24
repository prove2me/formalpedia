-- Prove2me | Theorems.Thm_GlobalTheory_algHom_coe_mvPolynomial
-- name    : GlobalTheory.algHom_coe_mvPolynomial
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:05:45.170937+00:00
-- url     : https://prove2.me/theorems/f6dbdc09-f8cb-46ff-9c52-42053f7be3be
-- title:
--   Global Theory: alg Hom coe mv Polynomial
-- statement:
--   The Global Theory construction uses the alg Hom coe mv Polynomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L106-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueFixedPointOfAdicContraction.lean#L106-L111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueFixedPointOfAdicContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open MvPowerSeries
variable {A S σ : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable [Finite σ]
omit [Finite σ]

theorem GlobalTheory.algHom_coe_mvPolynomial (φ : MvPowerSeries σ A →ₐ[A] S) (p : MvPolynomial σ A) :
    φ p = MvPolynomial.aeval (fun i => φ (X i)) p := by sorry
