-- Prove2me | Theorems.Thm_GlobalTheory_awayLiftAlgHom_algebraMap
-- name    : GlobalTheory.awayLiftAlgHom_algebraMap
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:06:35.847027+00:00
-- url     : https://prove2.me/theorems/d51b0e9d-6672-4210-9bfb-e5578f0a0e7e
-- title:
--   Global Theory: away Lift Alg Hom algebra Map
-- statement:
--   The Global Theory construction uses the away Lift Alg Hom algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInversionCoordinateLocalizationPolynomial.lean#L12-L15

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

theorem GlobalTheory.awayLiftAlgHom_algebraMap {k : Type} [Field k] {B : Type} [CommRing B] [Algebra k B]
    (P : k[X]) (f : k[X] →ₐ[k] B) (h : IsUnit (f P)) (q : k[X]) :
    awayLiftAlgHom P f h (algebraMap k[X] (Localization.Away P) q) = f q := by sorry
