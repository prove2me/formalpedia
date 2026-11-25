-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_cxSt
-- name    : GlobalTheory.CompanionTheory.HodgeCx.cxSt
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:02:12.529325+00:00
-- url     : https://prove2.me/theorems/237ab7fc-9c33-448d-b7ef-612377740794
-- title:
--   Hodge Cx: cx St
-- statement:
--   The Hodge Cx construction uses the cx St property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L93-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L93-L95

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DnCompDn
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeCx
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]

theorem GlobalTheory.CompanionTheory.HodgeCx.cxSt : CxSt := by sorry
