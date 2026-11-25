-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_smul
-- name    : GlobalTheory.IntSeries.intAA_smul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:10:55.348693+00:00
-- url     : https://prove2.me/theorems/cbcddd1a-63be-4bab-b748-801901ffa13d
-- title:
--   Int Series: int AA smul
-- statement:
--   The Int Series construction uses the int AA smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L50-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L50-L52

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

theorem GlobalTheory.IntSeries.intAA_smul (r : R) {f : MvPowerSeries σ k} (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (algebraMap R k r • f) := by sorry
