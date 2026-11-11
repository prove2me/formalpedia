-- Prove2me | Theorems.Thm_OAI_HarmonicArtin_ParabolicIntersections_null_boundary_contradiction_s236
-- name    : OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T20:06:08.376199+00:00
-- url     : https://prove2.me/theorems/76ed74b6-38dd-4941-a46b-cc6044e512e2
-- title:
--   OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction_s236: intermediate lemma from OpenAI, Parabolic intersections in Artin groups
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HarmonicArtin.ParabolicIntersections.unconditional_arbitrary_intersections`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_nonclique_dynamics`, `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_closure` and `OAI.HarmonicArtin.ParabolicIntersections.unconditional_parabolic_intersections`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Parabolic intersections in Artin groups*, OpenAI Math Release, September 23, 2026, result family 254, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction` of [lean/OAI/Topology/ArtinGroups/ParabolicIntersections/NullBoundary.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/NullBoundary.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.HarmonicArtin.ParabolicIntersections`, with `open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex`):
--
--   ```lean
--   theorem null_boundary_contradiction_s236 (D : IsolatedIterationData M)
--       (k : ℤ) (hk : k < D.q) (v : S ⊕ Unit)
--       (hv : v ∉ Sum.inl '' D.I)
--       (hinc : ∃ u ∈ Sum.inl '' D.I,
--         fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) v u < 0)
--       (hoccupied : ∀ z, D.valid z →
--         0 < fusionOrbitMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
--           (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
--           (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) z D.s k v)
--       (z : List ((S ⊕ Unit) × Bool)) (hz : D.valid z) (hc : D.capped z) : False
--   ```
--
--   **Definitions.** The statement is written with `OAI.HarmonicArtin.FiniteFusionEdge` (definitions bundle `OAIQ236Ap000` of this split); `OAI.HarmonicArtin.coxeterFusionEdge`, `OAI.HarmonicArtin.coxeterFusionEdge_diag`, `OAI.HarmonicArtin.coxeterFusionEdge_symm`, `OAI.HarmonicArtin.fusionFoldedCartan`, `OAI.HarmonicArtin.fusionLabelSize` and `OAI.HarmonicArtin.fusionLabelSize_ge_four` (definitions bundle `OAIQ236Ap003` of this split); `OAI.HarmonicArtin.IsolatedIterationData`, `OAI.HarmonicArtin.fusionOrbitMultiplicity` and `OAI.HarmonicArtin.IsolatedIterationData.capped` (definitions bundle `OAIQ236Ap008` of this split).
--
--   **Used by.** The proof of `OAI.HarmonicArtin.ParabolicIntersections.relative_descending_lower_connected_s236` of this split imports it.
-- source:
--   OpenAI, Parabolic intersections in Artin groups, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 254; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Parabolic-intersections-in-Artin-groups-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/ArtinGroups/ParabolicIntersections/NullBoundary.lean (declaration OAI.HarmonicArtin.ParabolicIntersections.null_boundary_contradiction)

import Mathlib
import Definitions.Def_OAIQ236Ap008

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
attribute [-simp] _root_.Convexity.StdSimplex.iConvexComb_single _root_.Convexity.StdSimplex.total_fin_two _root_.Convexity.StdSimplex.total_of_fintype _root_.Convexity.StdSimplex.weights_apply_eq_one _root_.Convexity.StdSimplex.weights_apply_le_one _root_.OAI.HarmonicArtin.ParabolicIntersections.pointedAction_generator _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.classMap_complex _root_.OAI.HarmonicArtin.ReversibleQuiver.ProbeEmbedding.matrix_identity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace HarmonicArtin.ParabolicIntersections

open ReversibleQuiver ReversibleQuiver.Zigzag ReversibleQuiver.Zigzag.BasedComplex

attribute [local instance] Classical.decEq Classical.propDecidable

variable {S : Type} [Fintype S] [LinearOrder S] {M : CoxeterMatrix S}

theorem null_boundary_contradiction_s236 (D : IsolatedIterationData M)
    (k : ℤ) (hk : k < D.q) (v : S ⊕ Unit)
    (hv : v ∉ Sum.inl '' D.I)
    (hinc : ∃ u ∈ Sum.inl '' D.I,
      fusionFoldedCartan (fusionLabelSize M) (coxeterFusionEdge M) v u < 0)
    (hoccupied : ∀ z, D.valid z →
      0 < fusionOrbitMultiplicity (fusionLabelSize M) (coxeterFusionEdge M)
        (coxeterFusionEdge_symm M) (coxeterFusionEdge_diag M)
        (fun e => le_trans (by norm_num) (fusionLabelSize_ge_four M e)) z D.s k v)
    (z : List ((S ⊕ Unit) × Bool)) (hz : D.valid z) (hc : D.capped z) : False := by
  sorry

end HarmonicArtin.ParabolicIntersections

end OAI
end
