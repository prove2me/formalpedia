-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_invariant_f_smooth
-- name    : OAI.AffineBernstein.affineEpigraph_invariant_f_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:04:55.602333+00:00
-- url     : https://prove2.me/theorems/53dcdafb-f4c4-4213-8b0f-8cb14ba54c38
-- title:
--   OAI.AffineBernstein.affineEpigraph_invariant_f_smooth: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_invariant_f_smooth` of [lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   lemma affineEpigraph_invariant_f_smooth {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
--       (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       ContDiffAt ℝ ∞ (invariantTubeF H bS bE δ) (s,e)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport` and `OAI.AffineBernstein.invariantTubeF` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.affineEpigraph_global_log_coordinate_identity`, `OAI.AffineBernstein.affineEpigraph_tube_angular_smooth`, `OAI.AffineBernstein.affineMaximal_global_d_identity`, `OAI.AffineBernstein.affineMaximal_invariant_tube_f_equation`, `OAI.AffineBernstein.affineMaximal_no_polynomial_logMeasure`, `OAI.AffineBernstein.affineMaximal_round_tube_f_equation` and `OAI.AffineBernstein.affineMaximal_tube_energy` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualInvariantTube.lean (declaration OAI.AffineBernstein.affineEpigraph_invariant_f_smooth)

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

lemma affineEpigraph_invariant_f_smooth {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) {e : E} (he : e ≠ 0)
    (bS : Module.Basis ι ℝ S) (bE : OrthonormalBasis (κ ⊕ Unit) ℝ E) (δ : ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    ContDiffAt ℝ ∞ (invariantTubeF H bS bE δ) (s,e) := by
  sorry

end AffineBernstein
end

end OAI
end
