-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_isUnit_det_red_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.isUnit_det_red_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:20:33.425351+00:00
-- url     : https://prove2.me/theorems/2edd2eb3-6bb5-4fc0-baf7-8bf9bebfad93
-- title:
--   Unr Dens: is Unit det red one
-- statement:
--   The Unr Dens construction uses the is Unit det red one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L29-L35

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResidueAlgebraUnramified
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardHermitianRepresentationsResidueStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_CardUnimodularHermitianRepsLevelOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.isUnit_det_red_one {R : Type} [CommRing R] (ϖ : R) {a : ℕ}
    (x : Matrix (Fin a) (Fin a) R) (hx : IsUnit x.det) : IsUnit (red ϖ 1 x).det := by sorry
