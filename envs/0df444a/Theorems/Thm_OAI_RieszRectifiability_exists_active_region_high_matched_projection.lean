-- Prove2me | Theorems.Thm_OAI_RieszRectifiability_exists_active_region_high_matched_projection
-- name    : OAI.RieszRectifiability.exists_active_region_high_matched_projection
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T19:23:13.435501+00:00
-- url     : https://prove2.me/theorems/9150d377-3e69-4669-a9a4-df306c369892
-- title:
--   OAI.RieszRectifiability.exists_active_region_high_matched_projection: intermediate lemma from OpenAI, Riesz transforms and uniform rectifiability in higher codimension
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.RieszRectifiability.quantitative_higher_codimension_riesz_rectifiability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Riesz transforms and uniform rectifiability in higher codimension*, OpenAI Math Release, September 24, 2026, result family 81, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.RieszRectifiability.exists_active_region_high_matched_projection` of [lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionHighMatchedProjection.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionHighMatchedProjection.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.RieszRectifiability`, with `open MeasureTheory Metric Set`, `open scoped NNReal`):
--
--   ```lean
--   theorem exists_active_region_high_matched_projection {n d : ℕ}
--       (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
--       (z : (supportLatticeNets μ R hR k).points)
--       (Good : SupportCellDescendant μ R hR k z → Prop)
--       (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
--       (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
--       (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 4096)
--       (hfit : ∀ i, activeRegionCell Good i →
--         bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
--       (f : S (supportCellRoot μ R hR k z) → Ambient d)
--       (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
--       (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
--       (hrsmall : r ≤ latticeRadius R k / 2097152)
--       (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p) :
--       ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
--         (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
--           infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
--             (4194304 * activeProjectionError d ε) * r) ∧
--         closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
--           P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16))
--   ```
--
--   **Definitions.** The statement is written with `OAI.RieszRectifiability.IsActiveRegionLimitModel`, `OAI.RieszRectifiability.IsAffineNPlane`, `OAI.RieszRectifiability.SupportCellDescendant`, `OAI.RieszRectifiability.activeProjectionError`, `OAI.RieszRectifiability.activeRegionCell`, `OAI.RieszRectifiability.bilateralPlaneError`, `OAI.RieszRectifiability.cellRegionStoppingScale`, `OAI.RieszRectifiability.latticeRadius`, `OAI.RieszRectifiability.supportCellRoot`, `OAI.RieszRectifiability.supportLatticeNets`, `OAI.RieszRectifiability.SeparatedCover` and `OAI.RieszRectifiability.SupportCellDescendant.radius` (definitions bundle `OAIQ231Rr000` of this split); `OAI.RieszRectifiability.Ambient` (the published bundle `Def_RieszQuantitative`).
--
--   **Used by.** The proof of `OAI.RieszRectifiability.quantitative_uniform_restart_surface_pieces` of this split imports it.
-- source:
--   OpenAI, Riesz transforms and uniform rectifiability in higher codimension, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 81; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Riesz-transforms-and-uniform-rectifiability-in-higher-codimension-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/RieszRectifiability/Restart/ActiveRegionHighMatchedProjection.lean (declaration OAI.RieszRectifiability.exists_active_region_high_matched_projection)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Analysis.Convex.GaugeRescale
import Mathlib.Analysis.Convex.Intrinsic
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic
import Mathlib.Topology.Defs.Basic
import Definitions.Def_RieszQuantitative
import Definitions.Def_OAIQ231Rr000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace RieszRectifiability

noncomputable section

open MeasureTheory Metric Set
open scoped NNReal

theorem exists_active_region_high_matched_projection {n d : ℕ}
    (μ : Measure (Ambient d)) (R : ℝ) (hR : 0 < R) (k : ℕ)
    (z : (supportLatticeNets μ R hR k).points)
    (Good : SupportCellDescendant μ R hR k z → Prop)
    (S : SupportCellDescendant μ R hR k z → AffineSubspace ℝ (Ambient d))
    (hS : ∀ i, IsAffineNPlane n (S i)) (ε : ℝ) (hε : 0 < ε)
    (hεtiny : ε ≤ 1 / 268435456) (hsmall : activeProjectionError d ε ≤ 1 / 4096)
    (hfit : ∀ i, activeRegionCell Good i →
      bilateralPlaneError μ i.center (1024 * i.radius) (S i) < ε)
    (f : S (supportCellRoot μ R hR k z) → Ambient d)
    (hmodel : IsActiveRegionLimitModel μ R hR k z Good S hS ε f)
    (p : Ambient d) (hp : p ∈ Set.range f) (r : ℝ) (hr : 0 < r)
    (hrsmall : r ≤ latticeRadius R k / 2097152)
    (hD : latticeRadius R (k + 1) ≤ cellRegionStoppingScale μ R hR k z Good p) :
    ∃ P : Submodule ℝ (Ambient d), Module.finrank ℝ P = n ∧
      (∀ x ∈ Set.range f ∩ closedBall p (1024 * r),
        infDist x (AffineSubspace.mk' p P : Set (Ambient d)) ≤
          (4194304 * activeProjectionError d ε) * r) ∧
      closedBall (P.orthogonalProjectionOnto p) (r / 32) ⊆
        P.orthogonalProjectionOnto '' (Set.range f ∩ closedBall p (r / 16)) := by
  sorry

end

end RieszRectifiability

end OAI
end
