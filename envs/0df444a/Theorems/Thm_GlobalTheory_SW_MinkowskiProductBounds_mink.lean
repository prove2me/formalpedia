-- Prove2me | Theorems.Thm_GlobalTheory_SW_MinkowskiProductBounds_mink
-- name    : GlobalTheory.SW.MinkowskiProductBounds.mink
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:42:50.922061+00:00
-- url     : https://prove2.me/theorems/9fb329fc-f2a9-42be-936a-1c9a7f438efa
-- title:
--   Minkowski Product Bounds: mink
-- statement:
--   The Minkowski Product Bounds construction uses the mink property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L13-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/ExistsShortIso.lean#L13-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroNormSqLeMulCovolumeRpow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsShortIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.MinkowskiProductBounds
open Module Submodule

theorem GlobalTheory.SW.MinkowskiProductBounds.mink {W V ι : Type} [AddCommGroup W] [Module ℝ W] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] (b : Basis ι ℝ W) (e : W ≃ₗ[ℝ] V)
    (Δ ε : ℝ) (hε : 0 < ε) : ∃ C : ℝ, ∀ T : W →ₗ[ℝ] W, LinearMap.det T ≠ 0 →
      |LinearMap.det T| ≤ Δ → (∀ x ∈ span ℤ (Set.range b), x ≠ 0 → ε ≤ ‖e (T x)‖) →
      ∃ v : Basis (Fin (finrank ℝ V)) ℝ W, ∀ i, v i ∈ span ℤ (Set.range b) ∧ ‖e (T (v i))‖ ≤ C := by sorry
