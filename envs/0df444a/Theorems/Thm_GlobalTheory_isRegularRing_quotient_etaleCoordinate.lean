-- Prove2me | Theorems.Thm_GlobalTheory_isRegularRing_quotient_etaleCoordinate
-- name    : GlobalTheory.isRegularRing_quotient_etaleCoordinate
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:01:51.5047+00:00
-- url     : https://prove2.me/theorems/5106412c-5127-42dc-8b3f-e42a60bd24f9
-- title:
--   Global Theory: is Regular Ring quotient etale Coordinate
-- statement:
--   The Global Theory construction uses the is Regular Ring quotient etale Coordinate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleCoordinateQuotientRegular.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleCoordinateQuotientRegular.lean#L9-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinateQuotientRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
open GlobalTheory

theorem GlobalTheory.isRegularRing_quotient_etaleCoordinate : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A]
    [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale →
    ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by sorry
