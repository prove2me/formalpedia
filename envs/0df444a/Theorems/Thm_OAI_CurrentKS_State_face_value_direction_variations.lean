-- Prove2me | Theorems.Thm_OAI_CurrentKS_State_face_value_direction_variations
-- name    : OAI.CurrentKS.State.face_value_direction_variations
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T22:51:20.368112+00:00
-- url     : https://prove2.me/theorems/e26d1edf-6d92-4e40-9868-f26bca0b3148
-- title:
--   OAI.CurrentKS.State.face_value_direction_variations: intermediate lemma from OpenAI, A polynomial-time construction of strong thin trees (result family 174)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A polynomial-time construction of strong thin trees (result family 174)*, OpenAI Math Release, September 23, 2026, result family 174, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CurrentKS.State`, with `open Matrix`, `open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter`, `open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff`):
--
--   ```lean
--   theorem face_value_direction_variations [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
--       (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
--       (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
--       (S₀ : H d) (K : ℝ) (hlo : -K • (Hermitian.one : H d) ≤ S₀+S A x)
--       (hhi : S₀+S A x ≤ K • (Hermitian.one : H d))
--       (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta c A x))
--       (hmin : ∀ w ∈ feasible (S₀+S A x) (eta c A x), objective ε z ≤ objective ε w)
--       (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
--       (hP : sandwich (invH z.2.1) P = eta c A x Q + ε • (Hermitian.one : H d))
--       (hQ : sandwich (invH z.2.2) Q = eta c A x P + ε • (Hermitian.one : H d)) :
--       ∃ U V : H d,
--         sandwich (invH z.2.1) U-eta c A x V = S A h+eta₁ c A x h z.2.2 ∧
--         sandwich (invH z.2.2) V-eta c A x U = -S A h+eta₁ c A x h z.2.1 ∧
--         deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s))) 0 =
--           ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) z.2.2)*inner ℝ (A i) P-
--             (1-c*psi₁ (x i)*inner ℝ (A i) z.2.1)*inner ℝ (A i) Q) ∧
--         deriv (deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s)))) 0 ≤
--           3*energy z.2.1 z.2.2 P Q U V-(c/2)*negativeWeight A x h z.2.1 z.2.2 P Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.CurrentKS.Hermitian.H`, `OAI.CurrentKS.Hermitian.Mat`, `OAI.CurrentKS.Hermitian.invH`, `OAI.CurrentKS.Hermitian.matrixRealInnerProduct`, `OAI.CurrentKS.Hermitian.one`, `OAI.CurrentKS.Hermitian.psdCone`, `OAI.CurrentKS.Hermitian.sandwich`, `OAI.CurrentKS.Scalar.psi₁`, `OAI.CurrentKS.State.Coordinates`, `OAI.CurrentKS.State.S`, `OAI.CurrentKS.State.energy`, `OAI.CurrentKS.State.eta`, `OAI.CurrentKS.State.eta₁`, `OAI.CurrentKS.State.line`, `OAI.CurrentKS.State.negativeWeight`, `OAI.CurrentKS.Variational.Point`, `OAI.CurrentKS.Variational.feasible`, `OAI.CurrentKS.Variational.objective`, `OAI.CurrentKS.Variational.value` and `OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH` (definitions bundle `OAIQ241TT002` of this split).
--
--   **Used by.** The proof of `OAI.CurrentKS.State.LightPoint.exists_descent_ensemble` of this split imports it.
-- source:
--   OpenAI, A polynomial-time construction of strong thin trees (result family 174), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 174; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/A-polynomial-time-construction-of-strong-thin-trees-September-23-2026/paper.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ241TT002

section

attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.State
noncomputable section
open CurrentKS.Hermitian CurrentKS.Scalar CurrentKS.Variational Matrix Set Filter
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d N : ℕ}

attribute [local instance] OAI.CurrentKS.State.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.State.instNormedSpaceRealSubtypeMatMemSubmoduleH_p3
attribute [local instance] OAI.CurrentKS.State.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.State.faceValueDirectionNormedAddCommGroup
attribute [local instance] OAI.CurrentKS.State.faceValueDirectionNormedSpace
theorem face_value_direction_variations [NeZero d] {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε)
    (A : Fin N → H d) (x h : Coordinates N) (hx : ∀ i, |x i| < 1)
    (hA : ∀ i, A i ∈ psdCone d) (hrank : ∀ i, (A i : Mat d).rank ≤ 1)
    (S₀ : H d) (K : ℝ) (hlo : -K • (Hermitian.one : H d) ≤ S₀+S A x)
    (hhi : S₀+S A x ≤ K • (Hermitian.one : H d))
    (z : Point d) (hz : z ∈ feasible (S₀+S A x) (eta c A x))
    (hmin : ∀ w ∈ feasible (S₀+S A x) (eta c A x), objective ε z ≤ objective ε w)
    (P Q : H d) (hPpos : P ∈ psdCone d) (hQpos : Q ∈ psdCone d)
    (hP : sandwich (invH z.2.1) P = eta c A x Q + ε • (Hermitian.one : H d))
    (hQ : sandwich (invH z.2.2) Q = eta c A x P + ε • (Hermitian.one : H d)) :
    ∃ U V : H d,
      sandwich (invH z.2.1) U-eta c A x V = S A h+eta₁ c A x h z.2.2 ∧
      sandwich (invH z.2.2) V-eta c A x U = -S A h+eta₁ c A x h z.2.1 ∧
      deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s))) 0 =
        ∑ i, h i*((1+c*psi₁ (x i)*inner ℝ (A i) z.2.2)*inner ℝ (A i) P-
          (1-c*psi₁ (x i)*inner ℝ (A i) z.2.1)*inner ℝ (A i) Q) ∧
      deriv (deriv (fun s => value ε (S₀+S A (line x h s)) (eta c A (line x h s)))) 0 ≤
        3*energy z.2.1 z.2.2 P Q U V-(c/2)*negativeWeight A x h z.2.1 z.2.2 P Q := by
  sorry

end
end CurrentKS.State

end OAI
end
