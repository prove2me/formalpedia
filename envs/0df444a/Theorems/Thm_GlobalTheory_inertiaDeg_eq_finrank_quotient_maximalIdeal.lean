-- Prove2me | Theorems.Thm_GlobalTheory_inertiaDeg_eq_finrank_quotient_maximalIdeal
-- name    : GlobalTheory.inertiaDeg_eq_finrank_quotient_maximalIdeal
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:47:04.122825+00:00
-- url     : https://prove2.me/theorems/77b68226-4957-5339-b02c-13b17f48824e
-- title:
--   Global Theory: inertia Deg eq finrank quotient maximal Ideal
-- statement:
--   The Global Theory construction uses the inertia Deg eq finrank quotient maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L254-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L254-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

theorem GlobalTheory.inertiaDeg_eq_finrank_quotient_maximalIdeal [Module.Finite R S] (n : Ideal S)
    [n.IsMaximal] :
    haveI := liesOver_maximalIdeal_of_isIntegral R S n
    n.inertiaDeg R = Module.finrank (R ⧸ maximalIdeal R) (S ⧸ n) := by sorry
