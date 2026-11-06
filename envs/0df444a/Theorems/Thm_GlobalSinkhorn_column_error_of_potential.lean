-- Prove2me | Theorems.Thm_GlobalSinkhorn_column_error_of_potential
-- name    : GlobalSinkhorn.column_error_of_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T04:23:08.733318+00:00
-- url     : https://prove2.me/theorems/67a53e24-f0c9-4f21-8b85-3c4a8bd0d204
-- title:
--   Eqs. (36)–(37) — $\Phi(w)\le\varepsilon^2/(16n^3)$ gives column error at most $\varepsilon/n$
-- statement:
--   Let $n\ge2$, let $S$ be a nonnegative doubly stochastic $n\times n$ matrix, let $w\in\mathbb R^n_{>0}$, and let $0<\varepsilon\le1$. If
--   $$
--   \Phi(w)\le\frac{\varepsilon^2}{16n^3},
--   $$
--   then every column sum of $M(w)=\operatorname{diag}((Sw)^{-1})S\operatorname{diag}(w)$ is within $\varepsilon/n$ of $1$:
--   $$
--   \Big|\sum_{i=1}^n(M(w))_{ij}-1\Big|\le\frac{\varepsilon}{n}\qquad\text{for every }j.
--   $$
--   Combined with $A^{(2t)}=M(w_t)$ and the decay of $\Phi(w_t)$, this gives the columnwise error bound (21) of Theorem 3.1.
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n} → Fin n (0-based); reason: Lean convention; same instances
--   - encoding: S nonnegative and doubly stochastic → S ∈ doublyStochastic ℝ (Fin n) (entries ≥ 0, all row and column sums 1); reason: Mathlib's doubly stochastic matrices are exactly the paper's
--   - encoding: M(w), F(w) defined with (Sw)⁻¹ and [Sᵀ(Sw)⁻¹]⁻¹ for w > 0 → Lean's total inverse in Mw, Fw; reason: for w > 0 and doubly stochastic S every inverted entry is positive (p.15), so the junk value 0 is never used
--   - encoding: ⟨v⟩ = (1/n) Σ_j v_j and componentwise powers/reciprocals → avg v = (Σ_j v j)/n, (w j)⁻¹, w j ^ 2; reason: notation of p.13 written out
--   - generalization: w = w_t, the t-th iterate, rescaled so that ⟨w⟩ = 1 → every w > 0 with Φ(w) ≤ ε²/(16n³); reason: the page's argument uses only Φ(w) ≤ ε²/(16n³), and M(w), Φ(w) are invariant under rescaling w; the iterate w_t is a special case
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), proof of Theorem 3.1, Eqs. (36)–(37), pp.20–21

import Mathlib
import Definitions.Def_GlobalSinkhorn_potential
import Definitions.Def_GlobalSinkhorn_Mw

open Matrix

namespace GlobalSinkhorn

/-- If `Φ(w) ≤ ε²/(16n³)`, then every column sum of `M(w)` is within `ε/n` of `1`.
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), proof of Theorem 3.1, Eqs. (36)–(37), pp.20–21. -/
theorem column_error_of_potential {n : ℕ} (hn : 2 ≤ n) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S ∈ doublyStochastic ℝ (Fin n)) (w : Fin n → ℝ) (hw : ∀ j, 0 < w j)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hΦ : potential w ≤ ε ^ 2 / (16 * (n : ℝ) ^ 3)) (j : Fin n) :
    |∑ i, Mw S w i j - 1| ≤ ε / n := by sorry

end GlobalSinkhorn
