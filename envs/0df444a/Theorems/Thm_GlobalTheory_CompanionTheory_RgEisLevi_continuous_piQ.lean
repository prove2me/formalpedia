-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEisLevi_continuous_piQ
-- name    : GlobalTheory.CompanionTheory.RgEisLevi.continuous_piQ
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:59:00.79288+00:00
-- url     : https://prove2.me/theorems/bc59e174-9429-41b9-9d95-1a49cf6513a7
-- title:
--   Rg Eis Levi: continuous pi Q
-- statement:
--   The Rg Eis Levi construction uses the continuous pi Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L228-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LeviDecompOfBlockDet.lean#L228-L234

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
variable [TopologicalSpace R] [IsTopologicalRing R]

theorem GlobalTheory.CompanionTheory.RgEisLevi.continuous_piQ (A : Ad E R) (ε : ℤˣ) : Continuous (piQ A ε (ι := ι)) := by sorry
