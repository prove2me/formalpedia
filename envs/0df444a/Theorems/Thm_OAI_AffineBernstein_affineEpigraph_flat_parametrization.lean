-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_flat_parametrization
-- name    : OAI.AffineBernstein.affineEpigraph_flat_parametrization
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:04:48.08181+00:00
-- url     : https://prove2.me/theorems/d1ac4a2a-ed81-4d51-8772-67f87b390d14
-- title:
--   OAI.AffineBernstein.affineEpigraph_flat_parametrization: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_flat_parametrization` of [lean/OAI/Analysis/AffineBernstein/FlatSupportImmersion.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/FlatSupportImmersion.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineEpigraph_flat_parametrization {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {B : Set S} (hB : IsOpen B)
--       (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
--       (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
--       (hJ : ∀ v, inner ℝ (J v).2 d = 0) :
--       let U := {x : Space n | (q₀+J x).1 ∈ B}
--       let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let X := fun x : Space n => a+L (supportParam Y (q₀+J x))
--       IsOpen U ∧ ContDiffOn ℝ ∞ X U ∧
--         (∀ x ∈ U, (X x).1 ∈ Ω ∧ (X x).2 = u (X x).1) ∧
--         (∀ x ∈ U, Function.Injective (fderiv ℝ X x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.gaussPoint` and `OAI.AffineBernstein.supportParam` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.affineEpigraph_flat_chart_global_area_lintegral`, `OAI.AffineBernstein.affineEpigraph_flat_graph_injective` and `OAI.AffineBernstein.affineMaximal_flatSupport_local_stationary` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/FlatSupportImmersion.lean (declaration OAI.AffineBernstein.affineEpigraph_flat_parametrization)

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
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

variable [CompleteSpace S] [FiniteDimensional ℝ E] [Nontrivial E]

theorem affineEpigraph_flat_parametrization {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {B : Set S} (hB : IsOpen B)
    (hK : ∀ s ∈ B, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ B, (0 : E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (q₀ : S × E) (d : E) (hd : inner ℝ q₀.2 d = 1)
    (J : Space n →L[ℝ] (S × E)) (hi : Function.Injective J)
    (hJ : ∀ v, inner ℝ (J v).2 d = 0) :
    let U := {x : Space n | (q₀+J x).1 ∈ B}
    let Y := fun q : S × E => gaussPoint {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let X := fun x : Space n => a+L (supportParam Y (q₀+J x))
    IsOpen U ∧ ContDiffOn ℝ ∞ X U ∧
      (∀ x ∈ U, (X x).1 ∈ Ω ∧ (X x).2 = u (X x).1) ∧
      (∀ x ∈ U, Function.Injective (fderiv ℝ X x)) := by
  sorry

end AffineBernstein
end

end OAI
end
