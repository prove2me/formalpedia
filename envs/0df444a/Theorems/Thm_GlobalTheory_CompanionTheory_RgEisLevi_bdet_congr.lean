-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_bdet_congr
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.bdet_congr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:58:49.553408+00:00
-- url     : https://prove2.me/theorems/66a9e446-d6b8-4fc1-b82b-40d22b094466
-- title:
--   Rg Eis Levi: bdet congr
-- statement:
--   The Rg Eis Levi construction uses the bdet congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L115-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L115-L125

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_ConvGrOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LeviDecompOfBlockDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEisLevi
variable {E R : Type} [Field E] [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
open Classical

theorem GlobalTheory.CompanionTheory.RgEisLevi.bdet_congr {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (s : Set κ) (t : Set κ')
    (e : s ≃ t) (g : GL κ' R) (m : GL κ R)
    (h : ∀ a b : s, (g : Matrix κ' κ' R) (e a).1 (e b).1 = (m : Matrix κ κ R) a.1 b.1) : bdet t g = bdet s m := by sorry
