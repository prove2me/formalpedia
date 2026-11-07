-- Prove2me | Theorems.Thm_GraphTensorCP_lemma_4_8
-- name    : GraphTensorCP.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:58.989444+00:00
-- url     : https://prove2.me/theorems/eb6301a7-5836-4a97-be8a-d16146340b24
-- title:
--   Lemma 4.8 — shifted tripling $P_\phi(\dots,3h+S)\ge3P_\phi(\dots,h)$ in every coordinate
-- statement:
--   For every integer $n\ge3$, every $\phi\in\Phi_{n,\mathbb F}$ and all positive integers $a_1,\dots,a_{n-2},h$, put $S=\sum_{j=1}^{n-2}(a_j-1)$. Then
--
--   $$P_\phi(a_1,\dots,a_{n-2},3h+S)\ge3\,P_\phi(a_1,\dots,a_{n-2},h).$$
--
--   By symmetry the analogous inequality holds in every input coordinate, with $S$ the sum of the other input degrees $a_i-1$.
--
--   Combined with concavity, the factor $3$ forces the profile to grow along the diagonal (Lemma 4.9).
--
--   **Formalization Note** Stated for every coordinate $j$: coordinate $j$ of a positive tuple $a$ is set to $h$ and to $3h+S$ with $S=\sum_{i\ne j}(a_i-1)$; $j=n-2$ is the displayed case.
--
--   Differences from the source:
--   - encoding: spectral points $\phi:\mathrm{Tens}_n(\mathbb F)\to\mathbb R_{\ge0}$ (Definition 2.19) → monotone semiring homomorphisms on the published quotient `MME.TensorQ` by mutual restriction (`Spec K n hn`); reason: a spectral point is constant on mutual-restriction classes and its four conditions are exactly "monotone semiring homomorphism"; same set of maps
--   - encoding: the displayed inequality in the last argument, plus the analogous inequality in every coordinate → one statement for every coordinate $j$ via `Function.update`; reason: the two clauses of the source are exactly the cases $j=n-2$ and general $j$
-- source:
--   H. Zhou, Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers, arXiv:2610.34273 (version of 2026-11-03), Lemma 4.8, p.41

import Mathlib
import Definitions.Def_GraphTensorCP_profile

universe u

namespace GraphTensorCP

/-- **Lemma 4.8** (shifted tripling inequality), Zhou, *Asymptotic Rank of Weighted Graph Tensors via Completely Positive Covers*, arXiv:2610.34273 (version of 2026-11-03), p.41:
"For every integer n ≥ 3, every ϕ ∈ Φ_{n,F}, and all positive integers a₁, . . . , a_{n−2}, h, put
S = Σ_{j=1}^{n−2}(a_j − 1). Then P_ϕ(a₁, . . . , a_{n−2}, 3h + S) ≥ 3P_ϕ(a₁, . . . , a_{n−2}, h). By symmetry,
the analogous inequality holds in every input coordinate, with S the sum of the other input
degrees."

**Formalization Note.** Stated for every input coordinate `j : Fin (n−1)`: the other arguments
are `a i` (`i ≠ j`) of a positive tuple `a`, coordinate `j` is set by `Function.update`, and
`S = Σ_{i ≠ j} (a i − 1)`. The case `j = n − 2` is the displayed inequality. `hn : 1 < n` only
types the spectrum. -/
theorem lemma_4_8 {K : Type u} [Field K] {n : ℕ} (hn : 1 < n) (hn3 : 3 ≤ n) (φ : Spec K n hn) :
    ∀ (j : Fin (n - 1)) (a : Fin (n - 1) → ℕ), (∀ i, 0 < a i) → ∀ h : ℕ, 0 < h →
      3 * profile φ (Function.update a j h) ≤
        profile φ (Function.update a j (3 * h + ∑ i ∈ Finset.univ.erase j, (a i - 1))) := by sorry

end GraphTensorCP
