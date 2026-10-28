-- Prove2me | Theorems.Thm_OAI_CannonRelease_boundary_record_scalar_limit
-- name    : OAI.CannonRelease.boundary_record_scalar_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T12:52:16.982705+00:00
-- url     : https://prove2.me/theorems/4804da4b-052a-44a2-a80f-cdbb39b8f86b
-- title:
--   OAI.CannonRelease.boundary_record_scalar_limit: intermediate lemma from OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CannonRelease.cannon`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A Modulus Proof of Cannon's Conjecture (result family 246)*, OpenAI Math Release, September 23, 2026, result family 246, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CannonRelease.boundary_record_scalar_limit` of [lean/OAI/Geometry/Cannon/Cannon/ScalarLimits/BoundaryRecordScalarLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/ScalarLimits/BoundaryRecordScalarLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CannonRelease`, with `open Set Topology`, `open Set Topology Filter Metric unitInterval`, `open scoped InnerProductSpace`, `open Set Metric Topology`, `open Set Topology unitInterval`, `open scoped BigOperators`, `open Set unitInterval`, `open Set MeasureTheory`, `open Set Filter Metric Topology`, `open Set Filter Topology`, `open Set Filter MeasureTheory Topology`, `open Set Filter Topology TopologicalSpace Metric`, `open scoped NNReal ENNReal`, `open Set Metric`, `open CannonGraph CannonVisual CannonMagnification CannonApprox CannonPlanar CannonChart CannonCharts`, `open CannonGrid CannonCells Set Metric Filter Topology MeasureTheory`):
--
--   ```lean
--   theorem boundary_record_scalar_limit (φ : Boundary D ≃ₜ CannonRelease.SphereTwo) :
--       let _ := visualMetricSpace D hδ
--       let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
--       let _ : BorelSpace (Boundary D) := ⟨rfl⟩
--       let a := Real.exp (2*visualExponent δ)
--       let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
--       ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
--       ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D)
--       (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
--       (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
--       (lam : ℝ) (hlam : 1 ≤ lam)
--       (hunbounded : ∀ B : ℝ, ∃ n,
--         B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)/lam^n),
--       let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
--       ∃ e : Plane → Boundary D, ∃ he : IsOpenEmbedding e,
--         ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
--           (∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹*M (N j)) ∧
--           ∃ ρ : (j : ℕ) → ι (N j) → ℝ, ∃ m : ℕ → ℕ, ∃ hm : ∀ j, 0 < m j,
--           ∃ hρ : ∀ j i, 0 ≤ ρ j i,
--           ∃ hadm : ∀ j, Admissible
--               (fun i => (e ∘ squareMap) ⁻¹' ball (p (N j) i) (2*(a^(N j))⁻¹)) (ρ j),
--             (∀ j, (∑ i, (ρ j i)^2) ≤ A/M (N j)) ∧
--             (∀ j z, ∀ i : Index (3*m j), weight (3*m j) z i ≠ 0 →
--               dist ((e ∘ squareMap) z)
--                 ((e ∘ squareMap) (vertex (3*m j) (by have := hm j; omega) i)) < (a^(N j))⁻¹) ∧
--             let f := fun j => interiorScalar (e ∘ squareMap)
--               (he.isEmbedding.comp squareMap_embedding) (p (N j)) ((a^(N j))⁻¹)
--               (ρ j) (hρ j) (hadm j) (m j) (hm j)
--             let μ := fun j => CannonAtomic.atomic (p (N j)) (ρ j) (M (N j))
--               (by
--                 apply Real.sInf_nonneg
--                 rintro t ⟨w,_,rfl⟩
--                 exact sq_nonneg _)
--             ∃ u : C(interior (range (e ∘ squareMap)), ℝ),
--               (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
--               (∃ top bot, u top = 0 ∧ u bot = 1) ∧
--               ∃ ν : FiniteMeasure (Boundary D), (ν.mass : ℝ) ≤ A ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
--                 Tendsto (f ∘ ψ) atTop (𝓝 u) ∧ Tendsto (μ ∘ ψ) atTop (𝓝 ν)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CannonApprox.Admissible`, `OAI.CannonApprox.interiorScalar`, `OAI.CannonAtomic.atomic`, `OAI.CannonCells.familyVectors`, `OAI.CannonCells.modulus`, `OAI.CannonCharts.Plane`, `OAI.CannonCharts.macroFamily`, `OAI.CannonCharts.squareMap`, `OAI.CannonCharts.squareMap_embedding`, `OAI.CannonDuality.Admissible`, `OAI.CannonDuality.Weights`, `OAI.CannonGraph.Thin`, `OAI.CannonGrid.Index`, `OAI.CannonGrid.Square`, `OAI.CannonGrid.vertex` and `OAI.CannonGrid.weight` (definitions bundle `OAIQ046C000` of this split); `OAI.CannonVisual.visualExponent` (definitions bundle `OAIQ046C001` of this split); `OAI.CannonRelease.visualMetricSpace` (definitions bundle `OAIQ046C002` of this split); `OAI.CannonRelease.Boundary`, `OAI.CannonRelease.CayleyData`, `OAI.CannonRelease.SphereTwo`, `OAI.CannonRelease.instTopologicalSpaceBoundary` and `OAI.CannonRelease.CayleyData.graph` (the published bundle `Def_CannonGeometricAction`).
--
--   **Used by.** The proofs of `OAI.CannonRelease.boundary_modulus_subexponential` and `OAI.CannonRelease.boundary_record_data` of this split import it.
-- source:
--   OpenAI, A Modulus Proof of Cannon's Conjecture (result family 246), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 246; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-Modulus-Proof-of-Cannons-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Cannon/Cannon/ScalarLimits/BoundaryRecordScalarLimit.lean (declaration OAI.CannonRelease.boundary_record_scalar_limit)

import Mathlib
import Definitions.Def_CannonGeometricAction
import Definitions.Def_OAIQ046C002

section

attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
section
noncomputable section
section
section
section
section
section
open Set Topology
open Set Topology Filter Metric unitInterval
open scoped InnerProductSpace
open Set Metric Topology
open Set Topology unitInterval
open scoped BigOperators
open Set unitInterval
open Set MeasureTheory
open Set Filter Metric Topology
open Set Filter Topology
open Set Filter MeasureTheory Topology
open Set Filter Topology TopologicalSpace Metric
open scoped NNReal ENNReal
open Set Metric

namespace CannonRelease

open CannonGraph CannonVisual CannonMagnification CannonApprox CannonPlanar CannonChart CannonCharts
open CannonGrid CannonCells Set Metric Filter Topology MeasureTheory

universe v

variable {G : Type v} [Group G] [TopologicalSpace G] [DiscreteTopology G]

variable (D : CayleyData G) {δ : ℕ} (hδ : Thin D.graph δ)

theorem boundary_record_scalar_limit (φ : Boundary D ≃ₜ CannonRelease.SphereTwo) :
    let _ := visualMetricSpace D hδ
    let _ : MeasurableSpace (Boundary D) := borel (Boundary D)
    let _ : BorelSpace (Boundary D) := ⟨rfl⟩
    let a := Real.exp (2*visualExponent δ)
    let LE := 8*Real.exp (visualExponent δ*(4*(8*δ+6):ℕ))
    ∀ d : ℝ, 0 < d → d < diam (univ : Set (Boundary D)) → d ≤ 1/(LE*3^2) →
    ∀ (ι : ℕ → Type*) [∀ n, Fintype (ι n)] (p : ∀ n, ι n → Boundary D)
    (hpsep : ∀ n i j, i ≠ j → (a^n)⁻¹ ≤ dist (p n i) (p n j))
    (hpnet : ∀ n x, ∃ i, dist (p n i) x ≤ (a^n)⁻¹)
    (lam : ℝ) (hlam : 1 ≤ lam)
    (hunbounded : ∀ B : ℝ, ∃ n,
      B < modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)/lam^n),
    let M := fun n => modulus (fun i => ball (p n i) (2*(a^n)⁻¹)) (macroFamily d)
    ∃ e : Plane → Boundary D, ∃ he : IsOpenEmbedding e,
      ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ → ℕ, StrictMono N ∧ Tendsto (M ∘ N) atTop atTop ∧
        (∀ j l, l ≤ N j → M (N j-l) ≤ (lam^l)⁻¹*M (N j)) ∧
        ∃ ρ : (j : ℕ) → ι (N j) → ℝ, ∃ m : ℕ → ℕ, ∃ hm : ∀ j, 0 < m j,
        ∃ hρ : ∀ j i, 0 ≤ ρ j i,
        ∃ hadm : ∀ j, Admissible
            (fun i => (e ∘ squareMap) ⁻¹' ball (p (N j) i) (2*(a^(N j))⁻¹)) (ρ j),
          (∀ j, (∑ i, (ρ j i)^2) ≤ A/M (N j)) ∧
          (∀ j z, ∀ i : Index (3*m j), weight (3*m j) z i ≠ 0 →
            dist ((e ∘ squareMap) z)
              ((e ∘ squareMap) (vertex (3*m j) (by have := hm j; omega) i)) < (a^(N j))⁻¹) ∧
          let f := fun j => interiorScalar (e ∘ squareMap)
            (he.isEmbedding.comp squareMap_embedding) (p (N j)) ((a^(N j))⁻¹)
            (ρ j) (hρ j) (hadm j) (m j) (hm j)
          let μ := fun j => CannonAtomic.atomic (p (N j)) (ρ j) (M (N j))
            (by
              apply Real.sInf_nonneg
              rintro t ⟨w,_,rfl⟩
              exact sq_nonneg _)
          ∃ u : C(interior (range (e ∘ squareMap)), ℝ),
            (∀ x, u x ∈ Icc (0 : ℝ) 1) ∧
            (∃ top bot, u top = 0 ∧ u bot = 1) ∧
            ∃ ν : FiniteMeasure (Boundary D), (ν.mass : ℝ) ≤ A ∧ ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
              Tendsto (f ∘ ψ) atTop (𝓝 u) ∧ Tendsto (μ ∘ ψ) atTop (𝓝 ν) := by
  sorry

end CannonRelease

end

end
end
end
end
end
end
end
end

end OAI
end
