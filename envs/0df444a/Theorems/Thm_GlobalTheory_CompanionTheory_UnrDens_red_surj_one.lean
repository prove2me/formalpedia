-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_surj_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.red_surj_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:22:13.761409+00:00
-- url     : https://prove2.me/theorems/1975487c-3415-402c-8823-53f94d27414c
-- title:
--   Unr Dens: red surj one
-- statement:
--   The Unr Dens construction uses the red surj one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L22-L27

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

theorem GlobalTheory.CompanionTheory.UnrDens.red_surj_one {R : Type} [CommRing R] (ϖ : R) {a b : ℕ}
    (y : Matrix (Fin a) (Fin b) (R ⧸ lev ϖ 1)) : ∃ x, red ϖ 1 x = y := by sorry
