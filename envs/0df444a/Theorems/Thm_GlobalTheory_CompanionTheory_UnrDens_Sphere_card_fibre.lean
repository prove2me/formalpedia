-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_Sphere_card_fibre
-- name    : GlobalTheory.CompanionTheory.UnrDens.Sphere.card_fibre
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:02:36.631526+00:00
-- url     : https://prove2.me/theorems/e0d5c3e2-14b1-4e1d-b639-5a32393f7726
-- title:
--   Sphere: card fibre
-- statement:
--   The Sphere construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianVectorValuesCard.lean#L11-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianVectorValuesCard.lean#L11-L28

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardNonzeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NormFibreCardZeroStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnitStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianVectorValuesCard
import Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_NormUnit_card_fibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens GlobalTheory.CompanionTheory.UnrDens.Sphere

theorem GlobalTheory.CompanionTheory.UnrDens.Sphere.card_fibre {E : Type} [CommRing E] {τ : E →+* E} [Fintype E] {V : Type} [AddCommGroup V]
    [Module E V] [Finite V] (B : HermSp E τ V) {w : V} (hw : IsUnit (B.h w w)) (c : E) :
    Nat.card {v : V // B.h v v = c} =
      ∑ a : E, Nat.card {v : B.perp w // (B.perpForm hw).h v v = c - a * τ a * B.h w w} := by sorry
