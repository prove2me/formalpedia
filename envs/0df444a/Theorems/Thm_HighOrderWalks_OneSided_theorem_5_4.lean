-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_theorem_5_4
-- name    : HighOrderWalks.OneSided.theorem_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:27.845562+00:00
-- url     : https://prove2.me/theorems/4252a40e-88e5-4b14-84d3-10ffd48dd74d
-- title:
--   Theorem 5.4 (Mixing of the random walks), p. 17 — one-sided λ-expander: ‖M⁺_kφ‖ ≤ ((k+1)/(k+2) + (k+1)λ/2)‖φ‖ on C^k_0
-- statement:
--   Let $X$ be a pure $n$-dimensional finite simplicial complex with a weight function $m$, and let $0\le\lambda\le1$. Suppose $X$ is a one-sided $\lambda$-local spectral expander: for every $0\le k\le n-1$ and every $\tau\in X(k-1)$, the second largest eigenvalue of the non-lazy upper random walk on the vertices of the link $X_\tau$ is at most $\lambda$. Then for every $0\le k\le n-1$ and every $k$-cochain $\phi$ orthogonal to the constants, $\sum_{\sigma\in X(k)}m(\sigma)\phi(\sigma)=0$,
--   $$\|M^+_k\phi\|\le\Big(\frac{k+1}{k+2}+\frac{k+1}{2}\,\lambda\Big)\|\phi\| ,$$
--   where $M^+_k$ is the upper random walk on $k$-simplices and $\|\cdot\|$ the $m$-weighted norm on $k$-cochains.
--
--   The theorem bounds the nontrivial spectrum of the upper random walk on $k$-simplices, and hence its mixing rate, by local spectral data alone: the expansion of the links' $1$-skeleta.
--
--   **Formalization Note.** The eigenvalue condition on links is stated in Rayleigh-quotient form (`OneSidedLSE`, see the definitions file); it ranges over all faces of dimension $-1$ to $n-2$, including the empty face. The proof on p. 18 ends with "$\le\frac{k+1}{k+2}+(k+1)\lambda$", a slip; the statement and the preceding line give $\frac{k+1}{2}\lambda$, which is what is stated here. $k$ is a natural number with $k+1\le n$; a $k$-cochain is read on faces with $k+1$ vertices.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 17, Theorem 5.4

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Theorem 5.4 (Mixing of the random walks), p. 17: let `X` be a weighted pure `n`-dimensional
simplicial complex and `0 ≤ λ ≤ 1`. If `X` is a one-sided `λ`-local spectral expander, then for
every `0 ≤ k ≤ n - 1` and every `φ ∈ C^k_0(X, ℝ)`,
`‖M⁺_k φ‖ ≤ ((k+1)/(k+2) + ((k+1)/2) λ) ‖φ‖`. -/
theorem theorem_5_4 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) (hexp : OneSidedLSE X m n lam)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) (hφ : ip X m (k + 1) φ (fun _ => 1) = 0) :
    nrm X m (k + 1) (upperWalk X m φ) ≤
      (((k : ℝ) + 1) / ((k : ℝ) + 2) + ((k : ℝ) + 1) / 2 * lam) * nrm X m (k + 1) φ := by sorry

end HighOrderWalks.OneSided
