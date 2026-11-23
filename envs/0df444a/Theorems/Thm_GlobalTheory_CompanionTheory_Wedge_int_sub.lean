-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Wedge_int_sub
-- name    : GlobalTheory.CompanionTheory.Wedge.int_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:02:53.962828+00:00
-- url     : https://prove2.me/theorems/a3ba677a-95c2-438c-b1b0-446d459d6bf2
-- title:
--   Wedge: int sub
-- statement:
--   The Wedge construction uses the int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeBoundFinitePlaces.lean#L48-L53

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

theorem GlobalTheory.CompanionTheory.Wedge.int_sub [IsUltrametricDist K] {a b : Matrix ι κ K}
    (ha : ∀ i j, ‖a i j‖ ≤ 1) (hb : ∀ i j, ‖b i j‖ ≤ 1) : ∀ i j, ‖(a - b) i j‖ ≤ 1 := by sorry
