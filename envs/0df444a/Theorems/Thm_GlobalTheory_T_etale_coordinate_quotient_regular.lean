-- Prove2me | Theorems.Thm_GlobalTheory_T_etale_coordinate_quotient_regular
-- name    : GlobalTheory.T.etale_coordinate_quotient_regular
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:28:28.756174+00:00
-- url     : https://prove2.me/theorems/747ede3e-16cb-55f4-abab-ccc6d7b41f8f
-- title:
--   T: etale coordinate quotient regular
-- statement:
--   The T construction uses the etale coordinate quotient regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/EtaleCoordinateQuotientRegular.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/CoreStatements/PublishedTheorems/NadelVanishingPairs/NadelVanishingLemmas/EtaleCoordinateQuotientRegular.lean#L5-L6

import Mathlib
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsRegularRingOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleCoordinateQuotientRegular
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_EtaleCoordinateQuotientRegular
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem GlobalTheory.T.etale_coordinate_quotient_regular : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] [Algebra (ZMod p) A] {n : ℕ} (t : Fin n → A), (MvPolynomial.aeval (R := ZMod p) t).toRingHom.Etale → ∀ j : Fin n, IsRegularRing (A ⧸ Ideal.span {t j}) := by sorry
