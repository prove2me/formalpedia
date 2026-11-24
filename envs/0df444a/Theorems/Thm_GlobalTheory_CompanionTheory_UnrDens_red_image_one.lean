-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_red_image_one
-- name    : GlobalTheory.CompanionTheory.UnrDens.red_image_one
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:20:26.660729+00:00
-- url     : https://prove2.me/theorems/934139ec-14cc-4362-978e-3e21365e3402
-- title:
--   Unr Dens: red image one
-- statement:
--   The Unr Dens construction uses the red image one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/CardUnimodularHermitianRepsLevelOne.lean#L37-L53

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

theorem GlobalTheory.CompanionTheory.UnrDens.red_image_one {R : Type} [CommRing R] (σ : R →+* R) (ϖ : R) (h : σ ϖ = ϖ) {m n : ℕ}
    (S : Matrix (Fin m) (Fin m) R) (T : Matrix (Fin n) (Fin n) R) :
    red ϖ 1 '' {x : Matrix (Fin m) (Fin n) R | red ϖ 1 (cT σ x * S * x) = red ϖ 1 T} =
      {y | cT (barσ σ ϖ h 1) y * red ϖ 1 S * y = red ϖ 1 T} := by sorry
