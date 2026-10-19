-- Prove2me | Theorems.Thm_HyperKCut_Structure_lemma_3_1
-- name    : HyperKCut.Structure.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:19.51849+00:00
-- url     : https://prove2.me/theorems/46e1ed54-9feb-41d0-9ce0-a9a9401dea15
-- title:
--   Lemma 3.1 — refining a (p+2)-partition by Q raises σ by at most d(Q) − d(W₀ ∩ Q)
-- statement:
--   Let $G=(V,E)$ be a finite unit-cost hypergraph, let $p\ge1$, and let $(X_1,\ldots,X_p,W_0,Z_0)$ be a partition of $V$ into nonempty, pairwise disjoint sets. Let $Q\subseteq V$ be such that the sets
--
--   1. $Y_i:=X_i\setminus Q$ for $i\in[p]$,
--   2. $Y_{p+1}:=Q\cap Z_0$,
--   3. $Z:=Z_0\setminus Q$,
--   4. $W:=W_0\cup(Q\setminus Z_0)$
--
--   are all nonempty. Then $(Y_1,\ldots,Y_p,Y_{p+1},W,Z)$ is a partition of $V$ and
--
--   $$\sigma(Y_1,\ldots,Y_{p+1},W,Z)\le\sigma(X_1,\ldots,X_p,W_0,Z_0)+d(Q)-d(W_0\cap Q).$$
--
--   This is the step of the induction that passes from a $(p+2)$-partition to a $(p+3)$-partition in the proof of Lemma 3.2, controlling the increase of $\sigma$.
--
--   **Formalization Note** Counts are natural numbers, so the inequality is stated additively: $\sigma(Y,W,Z)+d(W_0\cap Q)\le\sigma(X,W_0,Z_0)+d(Q)$, which is equivalent to the printed one. The page's "$Q\subset V$" denotes a subset of $V$ (the paper writes $\subsetneq$ for strict inclusion); in any case $Z\ne\emptyset$ forces $Q\ne V$. The family $(Y_1,\ldots,Y_{p+1})$ is `Fin.snoc (fun i => X i \ Q) (Q ∩ Z₀)`, indexed by `Fin (p+1)`.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 9 (PDF 10), Lemma 3.1

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 3.1, p. 9: refining (X₁, …, Xₚ, W₀, Z₀) by a set Q raises σ by at most d(Q) − d(W₀ ∩ Q). -/
theorem lemma_3_1 (H : Hypergraph V) (p : ℕ) (hp : 1 ≤ p)
    (X : Fin p → Finset V) (W₀ Z₀ : Finset V) (hX : IsPartitionYWZ X W₀ Z₀)
    (Q : Finset V)
    (hY : ∀ i, (X i \ Q).Nonempty) (hYp : (Q ∩ Z₀).Nonempty)
    (hZ : (Z₀ \ Q).Nonempty) (hW : (W₀ ∪ (Q \ Z₀)).Nonempty) :
    let Y : Fin (p + 1) → Finset V := Fin.snoc (α := fun _ => Finset V) (fun i => X i \ Q) (Q ∩ Z₀)
    let W : Finset V := W₀ ∪ (Q \ Z₀)
    let Z : Finset V := Z₀ \ Q
    IsPartitionYWZ Y W Z ∧
      sigma H Y W Z + d H (W₀ ∩ Q) ≤ sigma H X W₀ Z₀ + d H Q := by sorry

end HyperKCut.Structure
