-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_neg
-- name    : GlobalTheory.IntSeries.intAA_neg
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:29.900985+00:00
-- url     : https://prove2.me/theorems/bfcd2fc5-af70-48fb-a9c0-2f82ab948514
-- title:
--   Int Series: int AA neg
-- statement:
--   The Int Series construction uses the int AA neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L36-L38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_IntAASubstOfHasSubst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.IntSeries
variable {R : Type} [CommRing R] {k : Type} [CommRing k] [Algebra R k] {σ τ : Type}

theorem GlobalTheory.IntSeries.intAA_neg {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (-f) := by sorry
