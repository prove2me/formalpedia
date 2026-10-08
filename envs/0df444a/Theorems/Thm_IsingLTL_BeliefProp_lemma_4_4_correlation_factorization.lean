-- Prove2me | Theorems.Thm_IsingLTL_BeliefProp_lemma_4_4_correlation_factorization
-- name    : IsingLTL.BeliefProp.lemma_4_4_correlation_factorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:17:41.44152+00:00
-- url     : https://prove2.me/theorems/009ad994-d872-4438-b110-8e3136abea22
-- title:
--   Simon-type factorization of tree correlations in a field (Lemma 4.4)
-- statement:
--   Let $\mathsf T$ be a (deterministic) rooted tree, $\beta\ge0$ and $\underline B\ge0$. If the edge $(i,j)$ is on the unique path from $\varnothing$ to $k\in\mathsf T(\ell)$, with $j$ a child of $i\in\partial\mathsf T(t)$, $t\ge0$, then
--   $$\langle x_\varnothing;x_k\rangle^{(\ell)}_\varnothing\le\cosh^2(2\beta+B_i)\,\langle x_\varnothing;x_i\rangle^{(t)}_\varnothing\,\langle x_j;x_k\rangle^{(\ell)}_j,$$
--   where $\langle\cdot\rangle^{(r)}_i$ is the expectation under the Ising distribution (free boundary) on the subtree $\mathsf T_i$ of $i$ and all its descendants in $\mathsf T(r)$, and $\langle x;y\rangle=\langle xy\rangle-\langle x\rangle\langle y\rangle$.
--
--   This generalizes Simon's inequality to nonzero fields on trees; iterating it along paths gives the exponential decay of correlations (4.13).
--
--   **Formalization Note** $\beta\ge0$ and $B\ge0$ are the paper's standing assumptions, used in the proof through the GHS inequality. $k$ may equal $j$.
-- source:
--   Dembo & Montanari, Ising Models on Locally Tree-Like Graphs, arXiv:0804.4726v3, p. 14, Lemma 4.4, eq. (4.10)

import Mathlib
import Definitions.Def_IsingLTL_BeliefProp_UlamHarrisTree

namespace IsingLTL.BeliefProp

/-- **Lemma 4.4** (Dembo–Montanari, arXiv:0804.4726v3, p. 14, eq. (4.10)). If the edge `(i, j)` is
on the unique path from `ø` to `k ∈ T(ℓ)`, with `j` a descendant of `i ∈ ∂T(t)`, `t ≥ 0`, then
`⟨x_ø; x_k⟩^{(ℓ)}_ø ≤ cosh²(2β + B_i) ⟨x_ø; x_i⟩^{(t)}_ø ⟨x_j; x_k⟩^{(ℓ)}_j`, where `⟨·⟩^{(r)}_i` is
the expectation under the Ising distribution on the subtree `T_i` of `i` and its descendants in
`T(r)` (free boundary) and `⟨x; y⟩ = ⟨xy⟩ − ⟨x⟩⟨y⟩`.

Formalization Note: the tree is deterministic, given by its offspring function `ω` in
Ulam–Harris form; `j = i ++ [a]` is a child of `i` lying in `T(ℓ)`, and `k` is a descendant of `j`
(or `j` itself) in `T(ℓ)`. `T_ø` in `T(r)` is `T(r)`. The hypotheses `β ≥ 0` and `B ≥ 0` are the
paper's standing assumptions (ferromagnetic model, nonnegative fields) under which its proof
applies the GHS inequality. -/
theorem lemma_4_4_correlation_factorization (ω : List ℕ → ℕ) (β : ℝ) (B : List ℕ → ℝ)
    (hβ : 0 ≤ β) (hB : ∀ w, 0 ≤ B w) (ℓ t : ℕ) (i : List ℕ) (a : ℕ) (k : List ℕ)
    (hi : i ∈ gen ω t) (hj : i ++ [a] ∈ ballTree ω ℓ) (hk : k ∈ ballTree ω ℓ)
    (hjk : i ++ [a] <+: k) :
    corrOn (ballTree ω ℓ) (isingTree ω β B ℓ false) [] k ≤
      Real.cosh (2 * β + B i) ^ 2 * corrOn (ballTree ω t) (isingTree ω β B t false) [] i *
        corrOn (subtreeAt ω ℓ (i ++ [a]))
          (isingOn treeGraph β B ∅ (subtreeAt ω ℓ (i ++ [a]))) (i ++ [a]) k := by sorry

end IsingLTL.BeliefProp
