-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_5_1
-- name    : GraphTensorCP.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:09.561209+00:00
-- url     : https://prove2.me/theorems/2eb0b9c7-91ea-42f6-a16d-c125e81c60fc
-- title:
--   Lemma 5.1 — quadratic spectral constraint $4\sum_{i<j}a_ia_jP^{(\phi)}_{i,j}\le(\sum_ia_i)^2$
-- statement:
--   Let $n\ge2$ and let $\mathbb F$ be any field. For every $\phi\in\Phi_{n,\mathbb F}$ and every $a=(a_1,\dots,a_n)\in\mathbb R^n_{\ge0}$,
--
--   $$4\sum_{1\le i<j\le n}a_ia_jP^{(\phi)}_{i,j}\le\Big(\sum_{i=1}^na_i\Big)^2.\qquad(8)$$
--
--   Equivalently, $J-2P^{(\phi)}$ is copositive, where $J$ is the all-one matrix: every spectral edge-weight matrix is feasible for the copositive program defining $U^\Delta_{\mathrm{CP}}$ (except for the path inequalities, which are Lemma 5.4).
--
--   Differences from the source:
--   - encoding: vertices $1,\dots,n$ → `Fin n` $=\{0,\dots,n-1\}$; reason: relabeling; same instances
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 5.1, p.45 (§5 preamble: n ≥ 2, F arbitrary)

import Mathlib
import Definitions.Def_GraphTensorCP_specWeight

universe u

namespace GraphTensorCP

/-- **Lemma 5.1** (quadratic spectral constraint), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.45 (standing assumptions of §5: n ≥ 2,
F arbitrary):
"For every ϕ ∈ Φ_{n,F} and every a = (a₁, . . . , a_n) ∈ ℝⁿ_{≥0}, 4 Σ_{1≤i<j≤n} a_i a_j P^{(ϕ)}_{i,j} ≤
( Σ_{i=1}^{n} a_i )². (8)"

**Formalization Note.** `a : Fin n → ℝ` with `0 ≤ a` (entrywise); the sum is over unordered pairs
`i < j`. -/
theorem lemma_5_1 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (φ : Spec K n hn) (a : Fin n → ℝ)
    (ha : 0 ≤ a) :
    4 * (∑ i, ∑ j, if i < j then a i * a j * specWeight φ i j else 0) ≤ (∑ i, a i) ^ 2 := by sorry

end GraphTensorCP
