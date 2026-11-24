-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GramWedge_posSemidef_smul_gram_sub
-- name    : GlobalTheory.CompanionTheory.GramWedge.posSemidef_smul_gram_sub
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:34.813872+00:00
-- url     : https://prove2.me/theorems/78abe243-9288-4164-b650-918330bf23b6
-- title:
--   Gram Wedge: pos Semidef smul gram sub
-- statement:
--   The Gram Wedge construction uses the pos Semidef smul gram sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L45-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MultiplicativityInfinitePlaces.lean#L45-L63

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MultiplicativityInfinitePlaces
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GramWedge

theorem GlobalTheory.CompanionTheory.GramWedge.posSemidef_smul_gram_sub {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by sorry
