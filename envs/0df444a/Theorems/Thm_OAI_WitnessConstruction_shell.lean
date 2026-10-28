-- Prove2me | Theorems.Thm_OAI_WitnessConstruction_shell
-- name    : OAI.WitnessConstruction.shell
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-26T14:47:36.362438+00:00
-- url     : https://prove2.me/theorems/76efc34f-883b-4ff9-9c91-d5db427fd462
-- title:
--   OAI.WitnessConstruction.shell: intermediate lemma from OpenAI, The optimal order of convex-body covering density
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoveringOrder.optimal_order`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The optimal order of convex-body covering density*, OpenAI Math Release, September 23, 2026, result family 92, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.WitnessConstruction.shell` of [lean/OAI/Geometry/TranslativeCovering/WitnessConstruction.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/WitnessConstruction.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.WitnessConstruction`, with `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal`, `open Set MeasureTheory ProbabilityTheory`, `open scoped Classical BigOperators ENNReal`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open Set Filter MeasureTheory`, `open scoped ENNReal Topology`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open scoped Classical BigOperators`, `open scoped Classical BigOperators`, `open scoped BigOperators Classical`, `open Set MeasureTheory SphericalLaw CapCost BlockSets PoissonDiagrams`, `open scoped BigOperators`):
--
--   ```lean
--   theorem shell {a l u₀ u W : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
--       (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hW : 0 < W) :
--       ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
--       ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
--       ∀ (I : Type u_1) [Fintype I] [DecidableEq I] [Nonempty I],Fintype.card I ≤ n^2 →
--       ∀ (e : Sphere n) (axes : I → Sphere n) (r : I → ℝ) (R : ℝ),
--       (∀ i,RadialShell.low a n ≤ r i) → (∀ i,r i ≤ RadialShell.high a n) →
--       (Fintype.card I:ℝ)+(∑ i,RadialCost.weight n a (r i)) ≤ W*R →
--       let μ := intensity e (1/a)
--       let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
--       ∃ (P : Finpartition (Finset.univ : Finset I)) (anchor : Finset I → I)
--         (E : Finset I → Set (Sphere n)),
--         (∀ S ∈ P.parts,anchor S ∈ S ∧ MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
--           E S ⊆ caps (anchor S) ∧
--           Real.exp (-K*Real.log n)*clipped μ caps (anchor S) ≤ μ.real (E S) ∧
--           0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
--         Real.exp (-A*R) ≤ (∏ S : P.parts,μ.real (E S)) ∧
--         (∏ S : P.parts,μ.real (E S)) ≤ 1 ∧
--         diagram μ (fun S : P.parts => E S) (fun S : P.parts => E S) ≤
--           (∏ S : P.parts,μ.real (E S))^2*Real.exp (2*A*R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.BlockSets.clipped`, `OAI.BlockSets.common`, `OAI.CapCost.intensity`, `OAI.PoissonDiagrams.diagram`, `OAI.RadialCost.weight`, `OAI.RadialShell.high`, `OAI.RadialShell.low`, `OAI.RadialShell.η`, `OAI.SphericalLaw.Space`, `OAI.SphericalLaw.Sphere` and `OAI.SphericalLaw.cap` (definitions bundle `OAIQ16Cd000` of this split).
--
--   **Used by.** The proof of `OAI.PatternTail.bound` of this split imports it.
-- source:
--   OpenAI, The optimal order of convex-body covering density, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 92; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Translative-covering-densities-of-order-n-log-n-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/TranslativeCovering/WitnessConstruction.lean (declaration OAI.WitnessConstruction.shell)

import Mathlib
import Definitions.Def_OAIQ16Cd000

section

attribute [-instance] _root_.OAI.SingleLatticeCovering.LatticeGeometry.prod_discrete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal
open Set MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
open Set Filter MeasureTheory
open scoped ENNReal Topology
open Set Filter MeasureTheory
open scoped ENNReal Topology
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

universe u_1

namespace WitnessConstruction
open Set MeasureTheory SphericalLaw CapCost BlockSets PoissonDiagrams
open scoped BigOperators

theorem shell {a l u₀ u W : ℝ} (ha : 1 < a) (hl : 0 < l) (hlt : l < 1/a)
    (hu₀ : 1/a < u₀) (hu : u₀ < u) (hu1 : u < 1) (hW : 0 < W) :
    ∃ K A : ℝ,0 < K ∧ 0 < A ∧ ∃ n₀ : ℕ,
    ∀ n : ℕ,n₀ ≤ n → ∀ [NeZero n] [Fact (2 ≤ n)],
    ∀ (I : Type u_1) [Fintype I] [DecidableEq I] [Nonempty I],Fintype.card I ≤ n^2 →
    ∀ (e : Sphere n) (axes : I → Sphere n) (r : I → ℝ) (R : ℝ),
    (∀ i,RadialShell.low a n ≤ r i) → (∀ i,r i ≤ RadialShell.high a n) →
    (Fintype.card I:ℝ)+(∑ i,RadialCost.weight n a (r i)) ≤ W*R →
    let μ := intensity e (1/a)
    let caps := fun i => cap (axes i).val ((1+3*RadialShell.η n)/r i)
    ∃ (P : Finpartition (Finset.univ : Finset I)) (anchor : Finset I → I)
      (E : Finset I → Set (Sphere n)),
      (∀ S ∈ P.parts,anchor S ∈ S ∧ MeasurableSet (E S) ∧ E S ⊆ common caps S ∧
        E S ⊆ caps (anchor S) ∧
        Real.exp (-K*Real.log n)*clipped μ caps (anchor S) ≤ μ.real (E S) ∧
        0 < μ.real (E S) ∧ μ.real (E S) ≤ 1/2) ∧
      Real.exp (-A*R) ≤ (∏ S : P.parts,μ.real (E S)) ∧
      (∏ S : P.parts,μ.real (E S)) ≤ 1 ∧
      diagram μ (fun S : P.parts => E S) (fun S : P.parts => E S) ≤
        (∏ S : P.parts,μ.real (E S))^2*Real.exp (2*A*R) := by
  sorry

end WitnessConstruction

end OAI
end
