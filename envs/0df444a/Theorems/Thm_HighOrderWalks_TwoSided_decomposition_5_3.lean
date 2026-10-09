-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_decomposition_5_3
-- name    : HighOrderWalks.TwoSided.decomposition_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:05.929179+00:00
-- url     : https://prove2.me/theorems/c9232f7f-39c5-4ab2-8784-fc753f1eb659
-- title:
--   §5.3, p. 18 — V^j_k ⊆ C^k_0, V^j_k ⊆ V^{j+1}_k, and C^k_0(X) = U^k_k ⊕ ⋯ ⊕ U^0_k orthogonally
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex and $0\le k\le n-1$, with the subspaces $V^j_k$, $U^j_k$ of $C^k(X,\mathbb R)$ defined in §5.3. Then:
--   1. $V^j_k\subseteq C^k_0(X)$ for every $0\le j\le k$;
--   2. $V^j_k\subseteq V^{j+1}_k$ for every $0\le j<j+1\le k-1$;
--   3. the decomposition
--   $$C^k_0(X)=U^k_k\oplus U^{k-1}_k\oplus\cdots\oplus U^0_k$$
--   is orthogonal: the spaces $U^j_k$, $0\le j\le k$, are pairwise orthogonal for the weighted inner product, and every $\phi\in C^k_0(X)$ is a sum $\phi=\sum_{j=0}^k u_j$ with $u_j\in U^j_k$.
--
--   This decomposition is the frame of the two-sided results: Theorem 5.6 shows that $d^*_kd_k$ acts on $U^j_k$ approximately as multiplication by $k+1-j$.
--
--   **Formalization Note.** The page states (1) as a consequence of Lemma 5.1 and (2) for $k\ge2$; for $k\le1$ statement (2) is vacuous. The direct sum is stated as pairwise weighted orthogonality plus existence of the decomposition; together with (1) this is the orthogonal direct sum decomposition of $C^k_0(X)$ (uniqueness of the summands follows from orthogonality). All spaces consist of cochains supported on $X(k)$ (see the definitions file).
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 18, §5.3 (unnumbered claims after the definition of V^j_k and U^j_k)

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

namespace HighOrderWalks.TwoSided

/-- §5.3, p. 18 (unnumbered): for `0 ≤ k ≤ n - 1`,
(a) `V^j_k ⊆ C^k_0(X)` for every `0 ≤ j ≤ k` (by Lemma 5.1);
(b) `V^j_k ⊆ V^{j+1}_k` for `0 ≤ j < j + 1 ≤ k - 1`;
(c) `C^k_0(X) = U^k_k ⊕ U^{k-1}_k ⊕ ⋯ ⊕ U^0_k` is an orthogonal decomposition: the `U^j_k` are
pairwise `m`-orthogonal and every `φ ∈ C^k_0(X)` is a sum `Σ_{j=0}^k u_j` with `u_j ∈ U^j_k`. -/
theorem decomposition_5_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) :
    (∀ j ≤ k, Vsp X m k j ⊆ C0 X m (k + 1)) ∧
      (∀ j, j + 1 < k → Vsp X m k j ⊆ Vsp X m k (j + 1)) ∧
      (∀ i ≤ k, ∀ j ≤ k, i ≠ j → ∀ u ∈ Usp X m k i, ∀ w ∈ Usp X m k j,
        HighOrderWalks.OneSided.ip X m (k + 1) u w = 0) ∧
      (∀ φ ∈ C0 X m (k + 1), ∃ u : ℕ → Finset V → ℝ,
        (∀ j ≤ k, u j ∈ Usp X m k j) ∧ φ = ∑ j ∈ Finset.range (k + 1), u j) := by sorry

end HighOrderWalks.TwoSided
