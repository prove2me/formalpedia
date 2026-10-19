-- Prove2me | Theorems.Thm_HyperKCut_Structure_proposition_3_1
-- name    : HyperKCut.Structure.proposition_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:08.941116+00:00
-- url     : https://prove2.me/theorems/e5226aff-82ad-4589-bed9-755faeeb0903
-- title:
--   Proposition 3.1 — d(Y₁ ∪ W) + d(Y₂ ∪ W) equals σ(Y₁, Y₂, W, Z)
-- statement:
--   Let $G=(V,E)$ be a finite unit-cost hypergraph and let $(Y_1,Y_2,W,Z)$ be a partition of $V$ into four nonempty, pairwise disjoint sets. Put $A_1:=Y_1\cup W$ and $A_2:=Y_2\cup W$. Then
--
--   $$d(A_1)+d(A_2)=\sigma(Y_1,Y_2,W,Z)=\operatorname{cost}(Y_1,Y_2,W,Z)+\operatorname{cost}(W,Z)+\alpha(Y_1,Y_2,W,Z)+\beta(Y_1,Y_2,Z),$$
--
--   where $d$ is the hypergraph cut function and $\operatorname{cost}(W,Z)$, $\alpha$, $\beta$ are the counts of the mission's definitions file.
--
--   This identity explains the choice of $\sigma$: for $p=2$ it is exactly the sum of two cut values, and it is the base case of the induction proving Lemma 3.2.
--
--   **Formalization Note** The pair $(Y_1,Y_2)$ is the two-entry family `![Y₁, Y₂]`, and "partition" is `IsPartitionYWZ`, i.e. the ordered tuple $(Y_1,Y_2,W,Z)$ has nonempty, pairwise disjoint parts covering $V$.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 8 (PDF 9), Proposition 3.1

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Proposition 3.1, p. 8: for a partition (Y₁, Y₂, W, Z), d(Y₁ ∪ W) + d(Y₂ ∪ W) = σ(Y₁, Y₂, W, Z). -/
theorem proposition_3_1 (H : Hypergraph V) (Y₁ Y₂ W Z : Finset V)
    (hP : IsPartitionYWZ ![Y₁, Y₂] W Z) :
    d H (Y₁ ∪ W) + d H (Y₂ ∪ W) = sigma H ![Y₁, Y₂] W Z := by sorry

end HyperKCut.Structure
