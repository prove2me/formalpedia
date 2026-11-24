-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bound_left
-- name    : GlobalTheory.CompanionTheory.RgEis.bound_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:57.334504+00:00
-- url     : https://prove2.me/theorems/98991143-d7ba-4a51-961c-8847521d8033
-- title:
--   Rg Eis: bound left
-- statement:
--   The Rg Eis construction uses the bound left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L73-L76

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgEis

theorem GlobalTheory.CompanionTheory.RgEis.bound_left {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    A * p * n ≤ (A + B) * (p + q) * n := by sorry
