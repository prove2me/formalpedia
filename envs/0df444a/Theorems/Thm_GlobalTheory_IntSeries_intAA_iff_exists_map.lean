-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_iff_exists_map
-- name    : GlobalTheory.IntSeries.intAA_iff_exists_map
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:10:28.809262+00:00
-- url     : https://prove2.me/theorems/bc462aba-7108-46a4-90d4-fee57146ab9a
-- title:
--   Int Series: int AA iff exists map
-- statement:
--   The Int Series construction uses the int AA iff exists map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L26-L30

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

theorem GlobalTheory.IntSeries.intAA_iff_exists_map {f : MvPowerSeries σ k} :
    IntAA (R := R) k f ↔ ∃ g : MvPowerSeries σ R, MvPowerSeries.map (algebraMap R k) g = f := by sorry
