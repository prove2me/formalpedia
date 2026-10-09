-- Prove2me | Theorems.Thm_HighOrderWalks_TwoSided_theorem_5_6
-- name    : HighOrderWalks.TwoSided.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:41:08.204086+00:00
-- url     : https://prove2.me/theorems/6697226d-1dba-4dbd-9417-1d0d7c64bd14
-- title:
--   Theorem 5.6, p. 19 — two-sided λ-expander: ‖d*_k d_k P_{U^j_k}φ − (k+1−j)P_{U^j_k}φ‖ ≤ ε_k‖P_{U^j_k}φ‖
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex that is a two-sided $\lambda$-local spectral expander, and let
--   $$\varepsilon_0=\lambda,\qquad \varepsilon_k=2k\big(1+2k\sqrt k\big)\varepsilon_{k-1}+(k+1)\lambda\quad(0<k\le n-1).$$
--   Assume $\varepsilon_k\le\dfrac{1}{2\big(1+2(k+1)\sqrt{k+1}\big)}$ for all $0\le k\le n-2$. Then for every $0\le k\le n-1$, every $0\le j\le k$ and every $\phi\in C^k_0(X)$,
--   $$\big\|d^*_kd_kP_{U^j_k}\phi-(k+1-j)P_{U^j_k}\phi\big\|\le\varepsilon_k\,\big\|P_{U^j_k}\phi\big\|,$$
--   where $P_{U^j_k}$ is the weighted orthogonal projection onto the subspace $U^j_k$ of §5.3.
--
--   The theorem says that $d^*_kd_k=(k+2)M^+_k$ acts on $U^j_k$ approximately as the scalar $k+1-j$; Corollary 5.8 and Theorem 5.9 read off the approximate spectrum of the upper random walk from it.
--
--   **Formalization Note.** $k$ is quantified inside the conclusion, with $k+1\le n$ for $0\le k\le n-1$ and $k+2\le n$ for $0\le k\le n-2$ (no natural-number subtraction). $P_{U^j_k}\phi$ is any $u$ with `IsWProj X m (k + 1) (Usp X m k j) φ u`, which determines $u$ uniquely. The constants are those printed on p. 19; `eps lam k` is $\varepsilon_k$. The page states no range for $\lambda$; two-sided expansion forces $\lambda\ge0$ once $n\ge1$.
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 19, Theorem 5.6

import Mathlib
import Definitions.Def_HighOrderWalks_TwoSided_Setting
import Definitions.Def_HighOrderWalks_TwoSided_Subspaces

namespace HighOrderWalks.TwoSided

/-- Theorem 5.6, p. 19: let `X` be a two-sided `λ`-local spectral expander and `ε_k` as in
`eps`. If `ε_k ≤ 1/(2(1 + 2(k+1)√(k+1)))` for all `0 ≤ k ≤ n - 2`, then for every
`0 ≤ k ≤ n - 1`, `0 ≤ j ≤ k` and `φ ∈ C^k_0(X)`, with `u = P_{U^j_k} φ` the `m`-weighted
orthogonal projection, `‖d*_k d_k u - (k + 1 - j) u‖ ≤ ε_k ‖u‖`. -/
theorem theorem_5_6 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : HighOrderWalks.OneSided.IsPureComplex X n) (m : Finset V → ℝ) (hm : HighOrderWalks.OneSided.IsWeight X n m)
    (lam : ℝ) (hexp : TwoSidedLSE X m n lam)
    (hsmall : ∀ k : ℕ, k + 2 ≤ n →
      eps lam k ≤ 1 / (2 * (1 + 2 * ((k : ℝ) + 1) * Real.sqrt ((k : ℝ) + 1)))) :
    ∀ k : ℕ, k + 1 ≤ n → ∀ j ≤ k, ∀ φ ∈ C0 X m (k + 1), ∀ u : Finset V → ℝ,
      IsWProj X m (k + 1) (Usp X m k j) φ u →
        HighOrderWalks.OneSided.nrm X m (k + 1) (HighOrderWalks.OneSided.dStar X m (HighOrderWalks.OneSided.dS X u) - ((k : ℝ) + 1 - (j : ℝ)) • u) ≤
          eps lam k * HighOrderWalks.OneSided.nrm X m (k + 1) u := by sorry

end HighOrderWalks.TwoSided
