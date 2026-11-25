-- Prove2me | Theorems.Thm_GlobalTheory_ZM_DwModel_dirMap_fst
-- name    : GlobalTheory.ZM.DwModel.dirMap_fst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:34.883422+00:00
-- url     : https://prove2.me/theorems/30f348ef-2d01-4b86-bbb4-a50859c4f187
-- title:
--   Dw Model: dir Map fst
-- statement:
--   The Dw Model construction uses the dir Map fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L96-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ModuliSpaces/NotIsGaloisCoverTrivial.lean#L96-L98

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

theorem GlobalTheory.ZM.DwModel.dirMap_fst {K : Type} [Field K] {n : ℕ} (lam : (Fin n → K) →ₗ[K] K) (x : TrivSqZeroExt K (Fin n → K)) :
    (dirMap lam x).fst = x.fst ∧ (dirMap lam x).snd = lam x.snd := by sorry
