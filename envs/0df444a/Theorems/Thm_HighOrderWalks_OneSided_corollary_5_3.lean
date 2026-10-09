-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_corollary_5_3
-- name    : HighOrderWalks.OneSided.corollary_5_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:06.421864+00:00
-- url     : https://prove2.me/theorems/fe2fce54-01ab-48b8-895f-43917c5f1c02
-- title:
--   Corollary 5.3, pp. 16–17 — ‖dφ‖² ≤ Σ_j (k+1−j + Σ_{i=j}^k (i+1)μ_i)‖φ^j‖² with ‖φ‖² = Σ_j ‖φ^j‖² (μ_i ≥ 0)
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex whose links of dimension at least one are connected, including $X$ itself, and $0\le k\le n-1$. Let $\mu_0,\dots,\mu_k\ge0$ be such that, for each $0\le i\le k$ and each $\tau\in X(i-1)$, the second largest eigenvalue of the non-lazy upper walk $(M')^+_{\tau,0}$ on the link $X_\tau$ is at most $\mu_i$. Then for every $\phi\in C^k_0(X,\mathbb R)$ there are $\phi^j\in C^j_0(X,\mathbb R)$, $0\le j\le k$, such that
--   $$\|\phi\|^2=\|\phi^k\|^2+\dots+\|\phi^0\|^2$$
--   and
--   $$\|d\phi\|^2\le\sum_{j=0}^{k}\Big(k+1-j+\sum_{i=j}^{k}(i+1)\mu_i\Big)\|\phi^j\|^2 .$$
--
--   This is the quantitative consequence of the Decomposition Theorem from which the mixing bound of Theorem 5.4 follows.
--
--   **Formalization Note.** The $\mu_i$ are nonnegative upper bounds for the page's $\mu_i$ (take $\mu_i:=\max(\mu_i,0)$); nonnegativity is inherited from Lemma 4.3, whose printed form is false for negative $\mu_k$. Connectivity is the existence of a path in the one-skeleton of each link of dimension at least one.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, pp. 16–17, Corollary 5.3

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Corollary 5.3, pp. 16–17, with the correction `0 ≤ μ_i`: every link of dimension at least one
is connected, and for `0 ≤ k ≤ n - 1`, if `μ_i ≥ 0`
bounds the second largest eigenvalue of `(M')⁺_{τ,0}` for every `τ ∈ X(i-1)`, `0 ≤ i ≤ k`, then
every `φ ∈ C^k_0(X, ℝ)` has `φ^j ∈ C^j_0(X, ℝ)` with `‖φ‖² = ‖φ^k‖² + … + ‖φ^0‖²` and
`‖dφ‖² ≤ Σ_{j=0}^k (k + 1 - j + Σ_{i=j}^k (i+1) μ_i) ‖φ^j‖²`. -/
theorem corollary_5_3 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (hconn : ∀ c : ℕ, c + 1 ≤ n → ∀ τ ∈ cells X c,
      ∀ u ∈ cells (link X τ) 1, ∀ v ∈ cells (link X τ) 1,
        Relation.ReflTransGen
          (fun a b : Finset V => a ∈ cells (link X τ) 1 ∧ b ∈ cells (link X τ) 1 ∧
            a ∪ b ∈ cells (link X τ) 2) u v)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0)
    (μ : ℕ → ℝ) (hμ : ∀ i ≤ k, 0 ≤ μ i ∧ LinkUpper X m i (μ i)) :
    ∃ phi : ℕ → Finset V → ℝ,
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      ip X m (k + 1) φ φ = ∑ j ∈ Finset.range (k + 1), ip X m (j + 1) (phi j) (phi j) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) ≤
        ∑ j ∈ Finset.range (k + 1),
          ((k : ℝ) + 1 - j + ∑ i ∈ Finset.Icc j k, ((i : ℝ) + 1) * μ i) *
            ip X m (j + 1) (phi j) (phi j) := by sorry

end HighOrderWalks.OneSided
