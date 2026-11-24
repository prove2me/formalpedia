-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_spMap_away_mem_basicOpen
-- name    : GlobalTheory.SecGlue.spMap_away_mem_basicOpen
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:51:27.716262+00:00
-- url     : https://prove2.me/theorems/91a52123-a04f-4e92-83f7-30e548284409
-- title:
--   Sec Glue: sp Map away mem basic Open
-- statement:
--   The Sec Glue construction uses the sp Map away mem basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenCoverAffineOpenSpec.lean#L7-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsBasicOpenCoverAffineOpenSpec.lean#L7-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasicOpenCoverAffineOpenSpec
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

theorem GlobalTheory.SecGlue.spMap_away_mem_basicOpen {S : Type} [CommRing S] (s : S)
    (x : Sp (Localization.Away s)) :
    (spMap (algebraMap S (Localization.Away s))).base x ∈ PrimeSpectrum.basicOpen s := by sorry
