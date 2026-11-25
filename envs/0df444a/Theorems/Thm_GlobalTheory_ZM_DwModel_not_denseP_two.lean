-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_not_denseP_two
-- name    : GlobalTheory.ZM.DwModel.not_denseP_two
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:30.980227+00:00
-- url     : https://prove2.me/theorems/d7cc5f25-8e7a-5206-a5f2-d907d77942be
-- title:
--   Dw Model: not dense P two
-- statement:
--   The Dw Model construction uses the not dense P two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L112-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel

theorem GlobalTheory.ZM.DwModel.not_denseP_two : ¬ DenseP ({Ideal.span {2}} : Set (Ideal ℤ)) := by sorry
