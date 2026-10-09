-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_corollary_5_3_one_sided
-- name    : HighOrderWalks.OneSided.corollary_5_3_one_sided
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:43:13.20705+00:00
-- url     : https://prove2.me/theorems/6cd666c4-3ac4-4520-8d08-5313ef258120
-- title:
--   Corollary 5.3 (in particular), p. 17 — one-sided λ-expander: ‖dφ‖² ≤ Σ_j (k+1−j + ((k+j+2)(k+1−j)/2)λ)‖φ^j‖²
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex whose links of dimension at least one are connected, including $X$ itself. Suppose $X$ is a one-sided $\lambda$-local spectral expander with $\lambda\ge0$, and let $0\le k\le n-1$. Then for every $\phi\in C^k_0(X,\mathbb R)$ there are $\phi^j\in C^j_0(X,\mathbb R)$, $0\le j\le k$, such that $\|\phi\|^2=\|\phi^k\|^2+\dots+\|\phi^0\|^2$ and
--   $$\|d\phi\|^2\le\sum_{j=0}^{k}\Big(k+1-j+\frac{(k+j+2)(k+1-j)}{2}\,\lambda\Big)\|\phi^j\|^2 .$$
--
--   This is the form of Corollary 5.3 used in the proof of Theorem 5.4.
--
--   **Formalization Note.** The hypothesis $\lambda\ge0$ is added (inherited from Lemma 4.3; Theorem 5.4 assumes it anyway). Connectivity is expressed by paths in the one-skeleton of every link of dimension at least one.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 17, Corollary 5.3 ("In particular")

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Corollary 5.3 ("In particular"), p. 17, with the correction `0 ≤ λ`: if every link of
dimension at least one is connected and `X` is a one-sided `λ`-local spectral expander, then
every `φ ∈ C^k_0(X, ℝ)` (`0 ≤ k ≤ n - 1`) has
`φ^j ∈ C^j_0(X, ℝ)` with `‖φ‖² = ‖φ^k‖² + … + ‖φ^0‖²` and
`‖dφ‖² ≤ Σ_{j=0}^k (k + 1 - j + ((k+j+2)(k+1-j)/2) λ) ‖φ^j‖²`. -/
theorem corollary_5_3_one_sided {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (hconn : ∀ c : ℕ, c + 1 ≤ n → ∀ τ ∈ cells X c,
      ∀ u ∈ cells (link X τ) 1, ∀ v ∈ cells (link X τ) 1,
        Relation.ReflTransGen
          (fun a b : Finset V => a ∈ cells (link X τ) 1 ∧ b ∈ cells (link X τ) 1 ∧
            a ∪ b ∈ cells (link X τ) 2) u v)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0)
    (lam : ℝ) (hlam : 0 ≤ lam) (hexp : OneSidedLSE X m n lam) :
    ∃ phi : ℕ → Finset V → ℝ,
      (∀ j ≤ k, ip X m (j + 1) (phi j) (fun _ => 1) = 0) ∧
      ip X m (k + 1) φ φ = ∑ j ∈ Finset.range (k + 1), ip X m (j + 1) (phi j) (phi j) ∧
      ip X m (k + 2) (dS X φ) (dS X φ) ≤
        ∑ j ∈ Finset.range (k + 1),
          ((k : ℝ) + 1 - j + ((k : ℝ) + j + 2) * ((k : ℝ) + 1 - j) / 2 * lam) *
            ip X m (j + 1) (phi j) (phi j) := by sorry

end HighOrderWalks.OneSided
