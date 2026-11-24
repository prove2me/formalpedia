-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_dn_comp_dn
-- name    : GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:25:47.257053+00:00
-- url     : https://prove2.me/theorems/333be3fe-0e71-46cc-b83f-3fd6231e5697
-- title:
--   Hodge Cx: dn comp dn
-- statement:
--   The Hodge Cx construction uses the dn comp dn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L70-L75

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
variable (F : C ⥤ CommAlgCat.{0} R)

theorem GlobalTheory.CompanionTheory.HodgeCx.dn_comp_dn (n : ℕ) : dn F (n + 1) ∘ₗ dn F n = 0 := by sorry
