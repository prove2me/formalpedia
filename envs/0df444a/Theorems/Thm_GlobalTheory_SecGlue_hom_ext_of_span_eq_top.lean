-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_hom_ext_of_span_eq_top
-- name    : GlobalTheory.SecGlue.hom_ext_of_span_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:44.161707+00:00
-- url     : https://prove2.me/theorems/ff7140de-f3a9-48f0-a7e0-fb7eeea561f0
-- title:
--   Sec Glue: hom ext of span eq top
-- statement:
--   The Sec Glue construction uses the hom ext of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecHomExtOfLocalizationAwaySpanEqTop.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SpecHomExtOfLocalizationAwaySpanEqTop.lean#L7-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpecHomExtOfLocalizationAwaySpanEqTop
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.hom_ext_of_span_eq_top (S : Type) [CommRing S] (ι : Type) (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (Y : Scheme.{0}) (a b : Sp S ⟶ Y)
    (h : ∀ i, spMap (algebraMap S (Localization.Away (s i))) ≫ a =
      spMap (algebraMap S (Localization.Away (s i))) ≫ b) :
    a = b := by sorry
