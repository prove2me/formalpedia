-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PerfectPairings_mulNat_succ
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings.mulNat_succ
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:14:22.755853+00:00
-- url     : https://prove2.me/theorems/2a5cecf5-3a4e-4b5b-af38-9b9c8854bebd
-- title:
--   Perfect Pairings: mul Nat succ
-- statement:
--   The Perfect Pairings construction uses the mul Nat succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PerfectPairings.lean#L56-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PerfectPairings.lean#L56-L57

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CocycleRightZeroThd
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PerfectPairings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings

theorem GlobalTheory.IndefiniteRowSideFullHecke.PerfectPairings.mulNat_succ {R : Type} [CommRing R] {d : ℕ} (G : FGLaw R d) (n : ℕ) :
    mulNat G (n + 1) = G.add (mulNat G n) (pt R d 0) := by sorry
