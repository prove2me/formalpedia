-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_tube_positive
-- name    : OAI.AffineBernstein.affineEpigraph_invariant_tube_positive
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:06:14.776765+00:00
-- url     : https://prove2.me/theorems/90782bd1-efd7-4312-b131-c81b0fa76bfd
-- title:
--   OAI.AffineBernstein.affineEpigraph_invariant_tube_positive: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_invariant_tube_positive` of [lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineEpigraph_invariant_tube_positive {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       (tubeBaseMatrix H (s,e) bS).PosDef ∧ 0 < tubeAngularDensity H (s,e) bE ∧ 0 < H (s,e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.tubeAngularDensity` and `OAI.AffineBernstein.tubeBaseMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.affineEpigraph_angular_literal_drift`, `OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity`, `OAI.AffineBernstein.affineEpigraph_invariant_f_smooth`, `OAI.AffineBernstein.affineEpigraph_sigma_normalization`, `OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral`, `OAI.AffineBernstein.affineEpigraph_tube_angular_pair_nonneg`, `OAI.AffineBernstein.affineEpigraph_tube_angular_smooth`, `OAI.AffineBernstein.affineEpigraph_whole_graph_area_bound`, `OAI.AffineBernstein.affineMaximal_global_d_identity`, `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure`, `OAI.AffineBernstein.affineMaximal_round_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_tube_energy`, `OAI.AffineBernstein.normalized_model_positive_log_mass` and `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean (declaration OAI.AffineBernstein.affineEpigraph_invariant_tube_positive)

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein

open Filter
open scoped Topology
variable {S E : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] in
theorem affineEpigraph_invariant_tube_positive {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (tubeBaseMatrix H (s,e) bS).PosDef ∧ 0 < tubeAngularDensity H (s,e) bE ∧ 0 < H (s,e) := by
  sorry

end AffineBernstein
end

end OAI
end
