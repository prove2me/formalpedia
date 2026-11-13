-- Prove2me | Theorems.Thm_OAI_KadisonKastler_exists_unitary_boundary_intertwiner
-- name    : OAI.KadisonKastler.exists_unitary_boundary_intertwiner
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T04:56:44.214499+00:00
-- url     : https://prove2.me/theorems/0eeb86a5-b4d6-4936-8852-d3c7cfa211eb
-- title:
--   OAI.KadisonKastler.exists_unitary_boundary_intertwiner: intermediate lemma from OpenAI, Universal strong Kadison–Kastler stability (result family 289)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KadisonKastler.universal_strong_stability`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Universal strong Kadison–Kastler stability (result family 289)*, OpenAI Math Release, September 23, 2026, result family 289, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KadisonKastler.exists_unitary_boundary_intertwiner` of [lean/OAI/Analysis/KadisonKastler/BoundaryIntertwiner.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BoundaryIntertwiner.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KadisonKastler`, with `open scoped CStarAlgebra BoundedContinuousFunction`):
--
--   ```lean
--   theorem exists_unitary_boundary_intertwiner
--       (α : G →* (B ≃⋆ₐ[ℂ] B))
--       (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
--       (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
--       (S : unitary (G →ᵇ B))
--       (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
--       (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
--       {δ : ℝ} (hδ : δ < 1) (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
--       ∃ L : unitary B, (∀ g, (L : B) * (U g : B) = S.val g * α g (L : B)) ∧
--         ‖(L : B) - 1‖ ≤ 2 * δ
--   ```
--
--   **Definitions.** The statement is written with `OAI.KadisonKastler.boundaryConstant` (definitions bundle `Q260K003` of this split); `OAI.KadisonKastler.BimoduleMean` and `OAI.KadisonKastler.boundaryTranslate` (definitions bundle `Q260K004` of this split); `OAI.KadisonKastler.boundaryIntertwinerFunctionCStar` (definitions bundle `Q260K005` of this split).
--
--   **Used by.** The proofs of `OAI_KadisonKastler_constructed_finiteFactor_spatial_of_matrixStages_and_boundary`, `OAI.KadisonKastler.exists_product_boundary_intertwiner`, `OAI.KadisonKastler.exists_unitary_embedding_of_invariant_group`, `OAI.KadisonKastler.exists_unitary_finiteMatrix_embedding`, `OAI.KadisonKastler.exists_unitary_invariantGroup_embedding_in_algebra` and `OAI.KadisonKastler.uniform_common_action_of_rescaled_graphs` of this split import it.
-- source:
--   OpenAI, Universal strong Kadison–Kastler stability (result family 289), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 289; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Universal-strong-Kadison-Kastler-stability-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/KadisonKastler/BoundaryIntertwiner.lean (declaration OAI.KadisonKastler.exists_unitary_boundary_intertwiner)

import Mathlib
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Topology.ContinuousMap.Bounded.Star
import Mathlib.Topology.MetricSpace.Cauchy
import Definitions.Def_Q260K003
import Definitions.Def_Q260K004
import Definitions.Def_Q260K005

section

attribute [-instance] _root_.OAI.BoundedHochschild.WeakAlgebra.closedSubalgebra_starOrderedRing _root_.OAI.Generator.Tracial.baseCompleteSpace _root_.OAI.Generator.Tracial.baseNormedAlgebraRat _root_.OAI.HochschildCStarQuotient.quotientNormedRing _root_.OAI.HochschildCStarQuotient.quotientSeminormedRing _root_.OAI.HochschildComparison.PartialUnitary.instPartialOrder _root_.OAI.HochschildComparison.PartialUnitary.instZero _root_.OAI.HochschildUltrapower.ultrapowerCStar _root_.OAI.HochschildUltrapower.ultrapowerOrder _root_.OAI.HochschildUltrapower.ultrapowerStarOrder _root_.OAI.KadisonKastler.FullMatrixCorner.spatialTransportSubspaceComplete _root_.OAI.KadisonKastler.rationalCoreModule _root_.OAI.KadisonKastler.rawOperatorFieldCStar _root_.OAI.KadisonKastler.weakOperatorRepresentativeCStar _root_.OAI.KadisonSimilarity.isClosed_comap_subtype _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_isClosed _root_.OAI.KadisonSimilarity.vonNeumannAlgebra_smulMemClass _root_.OAI.UltrapowerBridge.instStarRingTracialQuotient _root_.OAI.UltrapowerBridge.instStarTracialQuotient _root_.OAI.KadisonKastler.instMeasurableSpaceListNat_solutions _root_.OAI.KadisonSimilarity.vonNeumann_closed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

namespace OAI

namespace KadisonKastler

open scoped CStarAlgebra BoundedContinuousFunction

noncomputable section

variable {B : Type*} [CStarAlgebra B]

attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerStarOrder
variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]

attribute [local instance] OAI.KadisonKastler.boundaryIntertwinerFunctionCStar
theorem exists_unitary_boundary_intertwiner
    (α : G →* (B ≃⋆ₐ[ℂ] B))
    (m : BimoduleMean (boundaryConstant (G := G) (B := B)))
    (hm : ∀ g f, m.toCLM (boundaryTranslate α g f) = α g (m.toCLM f))
    (S : unitary (G →ᵇ B))
    (hS : ∀ g h, S.val g * α g (S.val h) = S.val (g * h))
    (U : G →* unitary B) (hU : ∀ g t, α g (U t : B) = (U t : B))
    {δ : ℝ} (hδ : δ < 1) (hclose : ∀ g, ‖S.val g - (U g : B)‖ ≤ δ) :
    ∃ L : unitary B, (∀ g, (L : B) * (U g : B) = S.val g * α g (L : B)) ∧
      ‖(L : B) - 1‖ ≤ 2 * δ := by
  sorry

end

end KadisonKastler

end OAI
end
