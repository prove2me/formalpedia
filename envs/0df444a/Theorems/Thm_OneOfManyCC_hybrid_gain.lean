-- Prove2me | Theorems.Thm_OneOfManyCC_hybrid_gain
-- name    : OneOfManyCC.hybrid_gain
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T07:54:58.488954+00:00
-- url     : https://prove2.me/theorems/d0c6181d-b387-4d57-bee7-b6088e10095c
-- title:
--   §5, proof of Lemma 5.2 — $p_k-p_0\ge 1/k$, and some step has $p_i-p_{i-1}\ge k^{-2}$
-- statement:
--   Let $R$ be a total relation on finite sets, $1\le k\le\min\{|A|,|B|\}$, and $P$ a protocol solving $\mathrm{OneOut}^{\neq}_k(R)$. Let $\mu$, $\nu$ be distributions on $A$, $B$ with $\mu(x)<k^{-2}$ for all $x$ and $\nu(y)<k^{-2}$ for all $y$. With $p_j$ the probability that Alice can force the hybrid set $L_j$ for $X\sim\mu^k$, $Y\sim\nu^k$,
--
--   $$p_k-p_0\ge 1-2\binom{k}{2}k^{-2}=\frac1k,$$
--
--   so there is an index $i\in[k]$ with
--
--   $$p_i-p_{i-1}\ge k^{-2}.$$
--
--   The hypothesis on point masses is the "Otherwise" case of the proof of Lemma 5.2. The tuples are drawn with possible repeats, and collisions are what the term $2\binom k2k^{-2}$ pays for.
--
--   Differences from the source:
--   - generalization: $P$ is the fixed optimal protocol for $\mathrm{OneOut}^{\neq}_k(R)$ → any protocol $P$ solving $\mathrm{OneOut}^{\neq}_k(R)$; reason: optimality is not used; the optimal $P$ is one such protocol
--   - encoding: a distribution on a finite set → a point of `stdSimplex ℝ X`, with $\mu(E)$ as `mass μ E`; reason: nonnegative weights summing to one; the probability of an event is the sum of its weights
--   - encoding: finite sets $A, B, O$ → Fintype types in `Type`; reason: every finite set is equivalent to a type in `Type`, and this lets the statement quantify over all of them
--   - encoding: positions $[k]=\{1,\dots,k\}$ → 0-based `Fin k`; reason: a relabelling; the paper's index $i$ is `i.val + 1`
--   - encoding: $\mathrm{Inj}_k(A)$ → the embeddings `Fin k ↪ A`; reason: injective maps from $k$ positions are exactly the $k$-tuples of pairwise distinct elements
--   - encoding: a node or leaf of $P$ → its path `List Bool` from the root; reason: leaves with equal labels stay different leaves
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, pp.10–11

import Mathlib
import Definitions.Def_OneOfManyCC_OneOut
import Definitions.Def_OneOfManyCC_Hybrid

namespace OneOfManyCC

/-- **The hybrid gain.**
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §5, proof of Lemma 5.2, p.11:
"Hence p_k − p_0 ≥ 1 − 2(k choose 2)k⁻² = 1/k, so some index i ∈ [k] satisfies p_i − p_{i−1} ≥ k⁻²."

**Formalization Note.** `μ`, `ν` are in the "Otherwise" case of the proof, all point masses below
`k⁻²`. `P` is any protocol solving `OneOut≠ₖ(R)`; the paper's `P` is optimal, and optimality is not
used. The index `i : Fin k` is the paper's `i.val + 1`. -/
theorem hybrid_gain {A B O : Type} [Fintype A] [Fintype B] [Fintype O] (R : A → B → O → Prop)
    (hR : IsTotal R) (k : ℕ) (hk₁ : 1 ≤ k) (hk : k ≤ min (Fintype.card A) (Fintype.card B))
    (P : Protocol (Fin k ↪ A) (Fin k ↪ B) (Fin k × O))
    (hP : P.SolvesOn (OneOut k R) Set.univ Set.univ)
    (μ : A → ℝ) (hμ : μ ∈ stdSimplex ℝ A) (ν : B → ℝ) (hν : ν ∈ stdSimplex ℝ B)
    (hμk : ∀ x, μ x < (k : ℝ)⁻¹ ^ 2) (hνk : ∀ y, ν y < (k : ℝ)⁻¹ ^ 2) :
    1 / (k : ℝ) ≤ P.hybridProb μ ν k - P.hybridProb μ ν 0 ∧
      ∃ i : Fin k,
        (k : ℝ)⁻¹ ^ 2 ≤ P.hybridProb μ ν (i.val + 1) - P.hybridProb μ ν i.val := by sorry

end OneOfManyCC
