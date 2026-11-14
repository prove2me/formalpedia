-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_signed_shearing_forces_horospherical_collision
-- name    : OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:45.386206+00:00
-- url     : https://prove2.me/theorems/1b669ccd-601a-4544-8157-e095e6dee79e
-- title:
--   OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision` of [lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingSignedCollision.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingSignedCollision.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter`, `open scoped Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem signed_shearing_forces_horospherical_collision
--       {n : ℕ} {i j : Fin n} (hij : i ≠ j)
--       {Z : Type*} [TopologicalSpace Z] [T2Space Z]
--       (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
--       (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
--       (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
--       (htop : Tendsto (fun m => |t m|) atTop atTop)
--       (a B : ℝ) (ha : 0 < a)
--       (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
--       (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B)
--       (hx : ∀ m, x m ∈ K)
--       (hy : ∀ m, rightAction (x m)
--         (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
--           Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
--       (heq : ∀ m, F (x m) = F (rightAction (x m)
--         (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
--           Matrix.SpecialLinearGroup.transvection hij (-t m)))) :
--       ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
--         a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
--         ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h)
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.RootHorosphereShape`, `OAI.DukePrimeDegree.rootShearSize` and `OAI.DukePrimeDegree.slMatrixDifference` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.integralGroup` and `OAI.PrimeDegreePackets.rightAction` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/ShearingSignedCollision.lean (declaration OAI.DukePrimeDegree.signed_shearing_forces_horospherical_collision)

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem signed_shearing_forces_horospherical_collision
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    {Z : Type*} [TopologicalSpace Z] [T2Space Z]
    (K : Set (X n)) (hK : IsCompact K) (F : X n → Z) (hF : ContinuousOn F K)
    (x : ℕ → X n) (g : ℕ → G n) (hg : Tendsto g atTop (𝓝 1))
    (t : ℕ → ℝ) (ht : ∀ m, t m ≠ 0)
    (htop : Tendsto (fun m => |t m|) atTop atTop)
    (a B : ℝ) (ha : 0 < a)
    (hsize : ∀ m, a ≤ rootShearSize hij (g m) (t m))
    (hsmall : ∀ m, ∀ u : ℝ, |u| ≤ |t m| → rootShearSize hij (g m) u ≤ B)
    (hx : ∀ m, x m ∈ K)
    (hy : ∀ m, rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)) ∈ K)
    (heq : ∀ m, F (x m) = F (rightAction (x m)
      (Matrix.SpecialLinearGroup.transvection hij (t m) * g m *
        Matrix.SpecialLinearGroup.transvection hij (-t m)))) :
    ∃ h : G n, h ≠ 1 ∧ RootHorosphereShape i j h ∧
      a ≤ slMatrixDifference h 1 ∧ slMatrixDifference h 1 ≤ B ∧
      ∃ z ∈ K, rightAction z h ∈ K ∧ F z = F (rightAction z h) := by
  sorry

end DukePrimeDegree

end

end OAI
end
