-- Prove2me | Theorems.Thm_GlobalTheory_IntSeries_main
-- name    : GlobalTheory.IntSeries.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:08:31.860476+00:00
-- url     : https://prove2.me/theorems/5a1d52e2-b4a5-4832-aa37-7d7e8ace617d
-- title:
--   Int Series: main
-- statement:
--   The Int Series construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L87-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/RingsOfIntegers/IntAASubstOfHasSubst.lean#L87-L95

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

theorem GlobalTheory.IntSeries.main : ∀ (R : Type) [CommRing R] (k : Type) [CommRing k] [Algebra R k],
  (∀ (σ : Type) (f g : MvPowerSeries σ k), IntAA (R := R) k f → IntAA (R := R) k g → IntAA (R := R) k (f + g) ∧ IntAA (R := R) k (f - g) ∧ IntAA (R := R) k (f * g)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ k) (s : σ), IntAA (R := R) k f → IntAA (R := R) k (pderiv k s f)) ∧
  (∀ (σ : Type) (f : MvPowerSeries σ R), IntAA (R := R) k (MvPowerSeries.map (algebraMap R k) f)) ∧
  (∀ (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ k) (f : MvPowerSeries σ k), (∀ s, constantCoeff (a s) = 0) → (∀ s, IntAA (R := R) k (a s)) → IntAA (R := R) k f → IntAA (R := R) k (MvPowerSeries.subst a f)) := by sorry
