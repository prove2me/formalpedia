-- Prove2me | Theorems.Thm_OAI_UniversalFInfinity_Brown_geometric_lifted_of_uniform
-- name    : OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:46:38.759682+00:00
-- url     : https://prove2.me/theorems/537ed152-ebf1-4986-8c72-2109ed2bfee7
-- title:
--   Brown's criterion, OpenAI's uniform-nullhomotopy variant — a group whose Milnor stages become nullhomotopic in larger stages has type F∞
-- statement:
--   Notation, following OpenAI's definitions.
--   - **Realizations.** For a simplicial complex $K$ on $V$ (Mathlib's `PreAbstractSimplicialComplex V`), `Simplicial.Space K` is its geometric realization: finitely supported $w : V \to \mathbb R_{\ge 0}$ with $\sum w = 1$ and support a face, with the topology coinduced from the standard simplices.
--   - **Milnor's complex.** For a group $G$, `Milnor.complex G` is the simplicial complex on $\mathbb N \times G$ whose faces are the nonempty finite sets with at most one vertex at each level.
--   - **Shapes and stages.** A *shape set* is a finite set $S$ of finite subsets of $\mathbb N \times G$ (`Milnor.Shapes G`). Its stage `Milnor.stage G S` is the subcomplex of faces of Milnor's complex contained in a left translate $g \cdot s = \{(n, g h) : (n, h) \in s\}$ of some $s \in S \cup \{\{(0, 1)\}\}$.
--   - **Inclusions.** For $S \subseteq T$, `Milnor.stageIncl G S T` is the inclusion of realizations `Simplicial.Space (stage G S)` $\to$ `Simplicial.Space (stage G T)`.
--
--   `HasTypeFInfinity H` (from the published bundle `Def_UniversalFInfinity`) says that $H$ has a classifying space of finite type. Precisely, there is a connected Hausdorff space $X$ with a CW structure having finitely many cells in each dimension, whose fundamental group is isomorphic to $H$, and which has a contractible covering space.
--
--   **Statement.** Let $G$ be a group (in `Type`) with the discrete topology. Suppose that for every shape set $S$ there are a shape set $T \supseteq S$ such that `Milnor.stageIncl G S T` is nullhomotopic. Then `ULift G` has type $F_\infty$ (`HasTypeFInfinity (ULift.{z} G)`, in any universe `Type z`).
--
--   This is OpenAI's uniform-nullhomotopy variant of Brown's criterion (Brown 1987) for type $F_\infty$, applied to the stages of Milnor's construction (Milnor 1956).
--
--   Lean: `OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform`, OpenAI's theorem of that name (in `lean/OAI/GroupTheory/UniversalGroup/UniverseTransport.lean`). `Milnor.Shapes`, `Milnor.stage`, `Milnor.stageIncl`, `Milnor.complex` and `Simplicial.Space` come from the definitions bundle `OAIQWUFI002` of this split, and `HasTypeFInfinity` from `Def_UniversalFInfinity`.
-- source:
--   K. S. Brown, Finiteness properties of groups, J. Pure Appl. Algebra 44 (1987), for the criterion; J. Milnor, Construction of universal bundles II, Ann. of Math. 63 (1956), for the construction; Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/UniverseTransport.lean (declaration OAI.UniversalFInfinity.Brown.geometric_lifted_of_uniform)

import Mathlib
import Definitions.Def_UniversalFInfinity
import Definitions.Def_OAIQWUFI002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric Topology BigOperators
open Set Metric Topology
open Set Topology
open Set Metric Topology
open scoped NNReal
open Set Metric Topology
open scoped NNReal ENNReal
open Set Metric Topology
open scoped TensorProduct

open Set Metric Topology
namespace UniversalFInfinity.Brown
open Set Topology
universe z
variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

include hunif in

theorem geometric_lifted_of_uniform : HasTypeFInfinity (ULift.{z} G) := by
  sorry
end UniversalFInfinity.Brown

end

end OAI
end
