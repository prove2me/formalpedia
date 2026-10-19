-- Prove2me | Theorems.Thm_HyperKCut_Structure_lemma_3_3
-- name    : HyperKCut.Structure.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:28.295663+00:00
-- url     : https://prove2.me/theorems/af06df4e-80f4-46fd-bf50-23ce6d63ed8a
-- title:
--   Lemma 3.3 — select k−1 parts with bounded crossing cost
-- statement:
--   Let $k\ge2$ and let $(Y_1,\ldots,Y_p,W,Z)$ be a partition of a finite hypergraph with $p\ge2k-2$. There are distinct indices $i_1,\ldots,i_{k-1}$ such that the $k$-partition consisting of the selected $Y$-parts and their complement has cost satisfying
--
--   $$2\operatorname{cost}\bigl(Y_{i_1},\ldots,Y_{i_{k-1}},V\setminus\textstyle\bigcup_{j=1}^{k-1}Y_{i_j}\bigr)\le\operatorname{cost}(Y_1,\ldots,Y_p,W,Z)+\alpha(Y_1,\ldots,Y_p,W,Z)+\beta(Y_1,\ldots,Y_p,Z).$$
--
--   The right side omits $\operatorname{cost}(W,Z)$, as in the paper. This aggregation bound supports Theorem 3.1.
--
--   **Formalization Note** The selected indices form an injective map; the complementary final part is formed from the original vertex set.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 14 (PDF 15), Lemma 3.3

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 3.3, p. 14: select k−1 Y-parts with twice the new cost bounded by the three counts. -/
theorem lemma_3_3 (H : Hypergraph V) (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (Y : Fin p → Finset V) (W Z : Finset V)
    (hP : IsPartitionYWZ Y W Z) :
    ∃ f : Fin (k - 1) → Fin p, Function.Injective f ∧
      2 * cost H (Fin.snoc (fun j => Y (f j))
        ((Finset.univ : Finset V) \ Finset.univ.biUnion (fun j : Fin (k - 1) => Y (f j)))) ≤
      costYWZ H Y W Z + alpha H Y W Z + beta H Y Z := by sorry

end HyperKCut.Structure
