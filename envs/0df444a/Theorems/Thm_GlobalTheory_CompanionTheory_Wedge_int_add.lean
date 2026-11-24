-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_add
-- name    : GlobalTheory.CompanionTheory.Wedge.int_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:21:24.854391+00:00
-- url     : https://prove2.me/theorems/a6beddab-5ee8-48de-b1f8-d9fe1a28e9e3
-- title:
--   Wedge: int add
-- statement:
--   The Wedge construction uses the int add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L44-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L44-L46

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ArchimedeanBaseChange_ArchimedeanBaseChangeProof_IsotropicMahlerBounds_LogAbsoluteWedges_WedgeSub
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeBoundFinitePlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Wedge
variable {K ι ι' κ κ' : Type} [NormedField K]

theorem GlobalTheory.CompanionTheory.Wedge.int_add [IsUltrametricDist K] {a b : Matrix ι κ K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a + b) i j‖ ≤ 1 := by sorry
