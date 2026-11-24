-- Prove2me | Theorems.Thm_GlobalTheory_T_specHom_ext_of_localizationAway_span_eq_top
-- name    : GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:59:21.684294+00:00
-- url     : https://prove2.me/theorems/0010398e-d8bd-417c-b7ad-4513908fe8e2
-- title:
--   T: spec Hom ext of localization Away span eq top
-- statement:
--   The T construction uses the spec Hom ext of localization Away span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecHomExtOfLocalizationAwaySpanEqTopStatement.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecHomExtOfLocalizationAwaySpanEqTopStatement.lean#L7-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.specHom_ext_of_localizationAway_span_eq_top : ∀ (S : Type) [CommRing S] (ι : Type) (s : ι → S), Ideal.span (Set.range s) = ⊤ →
    ∀ (Y : Scheme.{0}) (a b : Sp S ⟶ Y),
    (∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a = spMap (algebraMap S (Localization.Away (s i))) ≫ b) →
    a = b := by sorry
