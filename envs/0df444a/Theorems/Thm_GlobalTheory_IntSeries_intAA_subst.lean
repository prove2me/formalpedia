-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_intAA_subst
-- name    : GlobalTheory.IntSeries.intAA_subst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:18:54.864181+00:00
-- url     : https://prove2.me/theorems/1dbc5e57-f4c3-4e01-bb34-c59b0e4f4e2f
-- title:
--   Int Series: int AA subst
-- statement:
--   The Int Series construction uses the int AA subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L82-L85

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

theorem GlobalTheory.IntSeries.intAA_subst [Finite σ] {a : σ → MvPowerSeries τ k} {f : MvPowerSeries σ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (hai : ∀ s, IntAA (R := R) k (a s))
    (hf : IntAA (R := R) k f) : IntAA (R := R) k (MvPowerSeries.subst a f) := by sorry
