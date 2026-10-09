-- Prove2me | Theorems.Thm_HighOrderWalks_OneSided_corollary_3_7
-- name    : HighOrderWalks.OneSided.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T01:42:14.272248+00:00
-- url     : https://prove2.me/theorems/2d52bd00-b039-4d8b-a657-770f0a88936b
-- title:
--   Corollary 3.7, p. 9 — d*dφ = (k+2)M⁺φ and dd*φ = (k+1)M⁻φ
-- statement:
--   Let $X$ be a pure $n$-dimensional weighted simplicial complex, $0\le k\le n-1$, and $\phi$ a $k$-cochain. Then, on $X(k)$,
--   $$d^*d\phi=(k+2)\,M^+_k\phi\qquad\text{and}\qquad dd^*\phi=(k+1)\,M^-_k\phi .$$
--
--   The upper and lower random walks are thus the signless analogues of the upper and lower Laplacians of Hodge theory; in particular $M^\pm_k$ are self-adjoint and positive semidefinite.
--
--   **Formalization Note.** Both identities are stated pointwise at every face $\tau\in X(k)$ (`cells X (k + 1)`).
-- source:
--   Kaufman–Oppenheim, High Order Random Walks: Beyond Spectral Gap, arXiv:1707.02799v3, p. 9, Corollary 3.7

import Mathlib
import Definitions.Def_HighOrderWalks_OneSided_Setting

namespace HighOrderWalks.OneSided

/-- Corollary 3.7, p. 9: for `0 ≤ k ≤ n - 1` and a `k`-cochain `φ`, `d*dφ = (k+2) M⁺φ` and
`dd*φ = (k+1) M⁻φ` on `X(k)`. -/
theorem corollary_3_7 {V : Type*} [DecidableEq V] (X : Finset (Finset V)) (n : ℕ)
    (hX : IsPureComplex X n) (m : Finset V → ℝ) (hm : IsWeight X n m)
    (k : ℕ) (hk : k + 1 ≤ n) (φ : Finset V → ℝ) :
    (∀ τ ∈ cells X (k + 1), dStar X m (dS X φ) τ = ((k : ℝ) + 2) * upperWalk X m φ τ) ∧
      (∀ τ ∈ cells X (k + 1), dS X (dStar X m φ) τ = ((k : ℝ) + 1) * lowerWalk X m φ τ) := by sorry

end HighOrderWalks.OneSided
