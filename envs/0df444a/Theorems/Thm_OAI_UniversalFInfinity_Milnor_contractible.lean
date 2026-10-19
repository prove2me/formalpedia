-- Prove2me | Theorems.Thm_OAI_UniversalFInfinity_Milnor_contractible
-- name    : OAI.UniversalFInfinity.Milnor.contractible
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:47:24.904967+00:00
-- url     : https://prove2.me/theorems/176a0a79-ab3e-4771-9491-f727c017aa2f
-- title:
--   Milnor's construction — the infinite join space of a nonempty group is contractible
-- statement:
--   For a simplicial complex $K$ on a vertex set $V$ (Mathlib's `PreAbstractSimplicialComplex V`), `Simplicial.Space K` is its geometric realization. Its points are the finitely supported functions $w : V \to \mathbb R$ with $w \ge 0$, $\sum_v w(v) = 1$ and support a face of $K$. Its topology is coinduced from the standard simplices of the faces. For a type $G$, `Milnor.complex G` is the simplicial complex on $\mathbb N \times G$ whose faces are the nonempty finite sets on which the first coordinate is injective (at most one vertex at each level $n$). `Milnor.Space G` $=$ `Simplicial.Space (Milnor.complex G)` is OpenAI's simplicial model of Milnor's infinite join $G * G * G * \cdots$.
--
--   **Statement.** For every nonempty type $G$, `Milnor.Space G` is contractible (Mathlib's `ContractibleSpace`).
--
--   This is the contractibility of Milnor's construction (Milnor 1956), the space $EG$ of his universal bundle.
--
--   Lean: `OAI.UniversalFInfinity.Milnor.contractible`, OpenAI's lemma of that name (in `lean/OAI/GroupTheory/UniversalGroup/MilnorControl.lean`). `Milnor.Space`, `Milnor.complex` and `Simplicial.Space` (with its topology) come from the definitions bundle `OAIQWUFI002` of this split.
-- source:
--   J. Milnor, Construction of universal bundles II, Ann. of Math. 63 (1956); Lean proof: OpenAI, A universal group of type F∞, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 250; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-universal-group-of-type-F-infinity-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/GroupTheory/UniversalGroup/MilnorControl.lean (declaration OAI.UniversalFInfinity.Milnor.contractible)

import Mathlib
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

namespace UniversalFInfinity.Milnor

section
open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
variable {G : Type u}

local instance (priority := 2000) instDecidableEqProdNat_solutions_r461751_1_stmt (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)
lemma contractible [Nonempty G] : ContractibleSpace (Space G) := by
  sorry

end

open Set Metric Topology BigOperators UniversalFInfinity.Simplicial
open scoped Classical unitInterval
universe u v
end UniversalFInfinity.Milnor

end

end OAI
end
