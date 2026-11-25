-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_X
-- name    : GlobalTheory.IntSeries.intAA_X
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:08:05.980133+00:00
-- url     : https://prove2.me/theorems/393de576-dc3f-4d9d-9493-7ee0d901c1bf
-- title:
--   Int Series: int AA X
-- statement:
--   The Int Series construction uses the int AA X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L20-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L20-L21

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

theorem GlobalTheory.IntSeries.intAA_X (s : σ) : IntAA (R := R) k (X s : MvPowerSeries σ k) := by sorry
