-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_eq_aeval_X
-- name    : GlobalTheory.algebraMap_eq_aeval_X
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:06.876588+00:00
-- url     : https://prove2.me/theorems/6a5f37f5-eaa7-4059-b8e4-463c544c5b82
-- title:
--   Global Theory: algebra Map eq aeval X
-- statement:
--   The Global Theory construction uses the algebra Map eq aeval X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L26-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInversionCoordinateLocalizationPolynomial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory

theorem GlobalTheory.algebraMap_eq_aeval_X {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    [Algebra k[X] B] [IsScalarTower k k[X] B] (p : k[X]) :
    algebraMap k[X] B p = aeval (algebraMap k[X] B X) p := by sorry
