-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeCx_pulln_cof
-- name    : GlobalTheory.CompanionTheory.HodgeCx.pulln_cof
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:11.349155+00:00
-- url     : https://prove2.me/theorems/569af6ff-26f2-4573-b6e7-1e127b3b4d6f
-- title:
--   Hodge Cx: pulln cof
-- statement:
--   The Hodge Cx construction uses the pulln cof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L79-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DnCompDn.lean#L79-L83

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

theorem GlobalTheory.CompanionTheory.HodgeCx.pulln_cof {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}
    (m : CoefMap (RingHom.id R) F G) (n : ℕ) (i : Fin (n + 2)) (f : Cn F n) :
    pulln m (n + 1) (cof F n i f) = cof G n i (pulln m n f) := by sorry
