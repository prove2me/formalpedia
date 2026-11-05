-- Prove2me | Theorems.Thm_OAI_BoundedHochschild_differential_is_cocycle
-- name    : OAI.BoundedHochschild.differential_is_cocycle
-- status  : Proved
-- author  : @wurtle
-- created : 2026-11-04T14:43:39.918408+00:00
-- url     : https://prove2.me/theorems/ade90854-9778-494b-9467-5a6073c61859
-- title:
--   The Hochschild differential squares to zero
-- statement:
--   Let $M$ be a unital C*-algebra and $f$ a bounded $n$-linear map $M^n\to M$ (`Cochain M n`). Writing `differential f` for the bounded $(n+1)$-linear map whose values are the Hochschild differential $\partial f$, one has
--
--   $$(\partial\partial f)(v)=0\qquad\text{for all }v\in M^{n+2}.$$
--
--   **Formalization Note** The statement is verbatim from OpenAI's Lean development, with the listed `Definitions` imported in place of the upstream modules; the definitions are supporting code for this statement. Only the keyword `lemma`, where used upstream, becomes `theorem`, and a leading `include ... in` or `omit ... in` moves to the preamble. It is a step of the Lean proof of the vanishing of higher bounded Hochschild cohomology.
-- source:
--   OpenAI, Vanishing of higher bounded Hochschild cohomology, September 23, 2026, https://github.com/openai/math (paper: preprints/Vanishing-of-higher-bounded-Hochschild-cohomology-September-23-2026/paper.pdf; Apache License 2.0); Lean declaration `OAI.BoundedHochschild.differential_is_cocycle`, https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/BoundedHochschild/BarDifferential.lean#L160

import Mathlib
import Definitions.Def_KadisonRingroseSupport2

namespace OAI

noncomputable section

open scoped ComplexOrder
open Filter Topology
open Filter Topology Metric
open Filter Topology MeasureTheory
open scoped RealInnerProductSpace ENNReal
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory Filter Topology
open scoped ComplexOrder BoundedContinuousFunction
open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Function
open scoped NNReal
open scoped ComplexOrder BoundedContinuousFunction CStarAlgebra
open scoped ComplexOrder CStarAlgebra
open scoped BigOperators
namespace BoundedHochschild

variable {M : Type*} [CStarAlgebra M]

end BoundedHochschild

open scoped BigOperators
namespace BoundedHochschild
variable {M : Type*} [CStarAlgebra M]

theorem differential_is_cocycle {n : ℕ} (f : Cochain M n) (v : Fin (n+2) → M) :
    differentialValue (differential f) v=0 := by
  sorry

end BoundedHochschild
end
end OAI
