-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_NerveCoh_pb_apply
-- name    : GlobalTheory.CompanionTheory.NerveCoh.pb_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:02:17.340865+00:00
-- url     : https://prove2.me/theorems/337eb5ed-6f16-4b4f-8289-85903450052b
-- title:
--   Nerve Coh: pb apply
-- statement:
--   The Nerve Coh construction uses the pb apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L281-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ConeExOfAcyclic.lean#L281-L282

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ConeExOfAcyclic
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
open CategoryTheory Opposite
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.NerveCoh
variable {R : Type} [CommRing R]
variable {C C' D : Type} [Category.{0} C] [Category.{0} C'] [Category.{0} D]

theorem GlobalTheory.CompanionTheory.NerveCoh.pb_apply (Φ : C' ⥤ C) {F : C ⥤ ModuleCat.{0} R} {G : C' ⥤ ModuleCat.{0} R} (α : Φ ⋙ F ⟶ G) (n : ℕ)
    (f : MCn F n) (c : Fin (n + 1) ⥤ C') : pb Φ α n f c = (α.app (c.obj (Fin.last n))).hom (f (c ⋙ Φ)) := by sorry
