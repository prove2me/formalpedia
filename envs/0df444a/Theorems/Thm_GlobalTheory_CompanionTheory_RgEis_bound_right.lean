-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgEis_bound_right
-- name    : GlobalTheory.CompanionTheory.RgEis.bound_right
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:57:44.625322+00:00
-- url     : https://prove2.me/theorems/b301a4ac-a662-4017-9e3c-238bf2f3b787
-- title:
--   Rg Eis: bound right
-- statement:
--   The Rg Eis construction uses the bound right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L78-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean#L78-L81

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

theorem GlobalTheory.CompanionTheory.RgEis.bound_right {A B p q n : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hp : 0 ≤ p) (hq : 0 ≤ q) (hn : 0 ≤ n) :
    B * q * n ≤ (A + B) * (p + q) * n := by sorry
