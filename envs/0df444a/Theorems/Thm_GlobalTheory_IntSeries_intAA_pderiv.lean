-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_pderiv
-- name    : GlobalTheory.IntSeries.intAA_pderiv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:18:45.01686+00:00
-- url     : https://prove2.me/theorems/fcdd8778-89c6-4e01-8b7a-76f92346eadb
-- title:
--   Int Series: int AA pderiv
-- statement:
--   The Int Series construction uses the int AA pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L68-L71

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

theorem GlobalTheory.IntSeries.intAA_pderiv {f : MvPowerSeries σ k} (s : σ) (hf : IntAA (R := R) k f) :
    IntAA (R := R) k (pderiv k s f) := by sorry
