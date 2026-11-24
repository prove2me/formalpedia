-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_RT_CellSplit_lift_diag
-- name    : GlobalTheory.CompanionTheory.Ar.RT.CellSplit.lift_diag
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:20:57.312646+00:00
-- url     : https://prove2.me/theorems/b7f330f1-ea45-478e-b7e0-f8c09a6035cf
-- title:
--   Cell Split: lift diag
-- statement:
--   The Cell Split construction uses the lift diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L91-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/DivisibilityProofs/HermitianDarbouxSplitProduct.lean#L91-L97

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_FiniteNonunitMatrix
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_DivisibilityProofs_HermitianDarbouxSplitProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.RT GlobalTheory.CompanionTheory.Ar.RT.CellSplit
open GlobalTheory.WeilM

theorem GlobalTheory.CompanionTheory.Ar.RT.CellSplit.lift_diag {S E₁ E₂ β : Type} [CommRing S] [CommRing E₁] [CommRing E₂] (s : S ≃+* E₁ × E₂) [Fintype β]
    [DecidableEq β] (A : Matrix (β ⊕ β) (β ⊕ β) E₁) (B : Matrix β β E₁)
    (h : A * (diagCols β : Matrix (β ⊕ β) β E₁) = (diagCols β : Matrix (β ⊕ β) β E₁) * B) :
    lift s A * (diagCols β : Matrix (β ⊕ β) β S) = (diagCols β : Matrix (β ⊕ β) β S) * lift s B := by sorry
