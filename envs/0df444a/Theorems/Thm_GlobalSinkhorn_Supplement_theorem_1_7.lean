-- Prove2me | Theorems.Thm_GlobalSinkhorn_Supplement_theorem_1_7
-- name    : GlobalSinkhorn.Supplement.theorem_1_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:57:40.066746+00:00
-- url     : https://prove2.me/theorems/acec6e0d-0d69-4deb-abd1-5b555e0b81d6
-- title:
--   Theorem 1.7 — dense inputs: SK reaches error $\varepsilon$ in $O(\log n+\log(1/\varepsilon))$ iterations if $\sigma<\gamma\rho-\tau$ or $\gamma>1/2$
-- statement:
--   Fix $\gamma,\rho\in(0,1]$. For all sufficiently large $n$, let $D\in[0,1]^{n\times n}$ be $(\gamma,\rho)$-dense (every row and column has at least $\lceil\gamma n\rceil$ entries $\ge\rho$). Let $r=(D(1,[n]),\dots,D(n,[n]))$ and $c=(D([n],1),\dots,D([n],n))$ be its row and column sums,
--   $$
--   E=\operatorname{diag}(r)^{-1/2}\,D\,\operatorname{diag}(c)^{-1/2},\qquad\sigma=s_2(E).
--   $$
--   Run Sinkhorn–Knopp on the row-normalized input $A^{(0)}=\operatorname{diag}(r)^{-1}D$, one normalization per iteration. Then:
--
--   1. (a) if $\sigma<\gamma\rho-\tau$ for a positive constant $\tau$, SK achieves total marginal $\ell_1$ error $\varepsilon$ within $O_{\rho,\gamma,\tau}(\log n+\log(1/\varepsilon))$ iterations;
--   2. (b) if $\gamma>1/2$, SK achieves total marginal $\ell_1$ error $\varepsilon$ within $O_{\rho,\gamma}(\log n+\log(1/\varepsilon))$ iterations.
--
--   Part (b) recovers the density-above-$1/2$ guarantee; part (a) gives a spectral route to the same bound at any positive density.
--
--   **Formalization Note** The threshold $N$ for "sufficiently large $n$" depends only on $(\gamma,\rho)$ and is chosen before $\tau$. "Achieves the error $\varepsilon$ in $k$ iterations" means some iterate $A^{(t)}$ with $t\le k$ has $\sum_i|r_i-1|+\sum_j|c_j-1|\le\varepsilon$ (Eq. (14)). The $O$-constant $C$ depends on $(\gamma,\rho,\tau)$ in (a) and on $(\gamma,\rho)$ in (b).
--
--   Differences from the source:
--   - encoding: indices [n] = {1,…,n}, index sets I, J ⊆ [n] → Fin n (0-based), Finset (Fin n); [n] ∖ J is Jᶜ; |I| compared as a real number; reason: Lean convention; same instances
--   - encoding: s₂(·), second-largest singular value counted with multiplicity → the published GlobalSinkhorn.s2, i.e. (Matrix.toEuclideanLin ·).singularValues 1; reason: Mathlib's singular values are 0-indexed, nonincreasing, with multiplicity; index 1 is the second
--   - encoding: for all sufficiently large n → ∃ N : ℕ (depending on γ, ρ only, chosen before τ), ∀ n ≥ N; reason: the page fixes γ, ρ, then says 'for all sufficiently large n', then introduces τ in item (a)
--   - encoding: E = diag(r)^{-1/2} D diag(c)^{-1/2} → normalizedMatrix D; reason: the matrix written out; density gives positive row and column sums
--   - encoding: D ∈ [0,1]^{n×n} (γ, ρ)-dense → (∀ i j, 0 ≤ D i j ∧ D i j ≤ 1) ∧ IsDense γ ρ D; reason: the hypothesis written out with the density predicate of p.4
--   - encoding: the SK algorithm (on the row-normalized input, p.7 and proof p.63) with one normalization per iteration → skIter (rowNormalize D) t with the published skIter and rowNormalize; reason: p.7: 'for a general input with positive row sums, first normalize its rows'; the proof of Theorem 1.7 (p.63) runs SK on A = diag(r)⁻¹D
--   - reading: achieves the error ε in O(log n + log 1/ε) iterations → ∃ C > 0 (constant per item), ∃ t : ℕ, (t : ℝ) ≤ C (log n + log(1/ε)) ∧ marginalErr (skIter (rowNormalize D) t) ≤ ε; reason: the literal meaning of 'achieves … in k iterations' (some iterate within k steps), with 'achieve the ε error' as defined in (14), p.13
--   - reading: error ε, range not stated → 0 < ε ≤ 1; reason: the O(log n + log 1/ε) bound concerns small ε; the paper's convergence theorems (1.1, 1.5) and the proof (via Theorem 3.1) use 0 < ε ≤ 1
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), Theorem 1.7, pp.8–9 (error (14), p.13; SK input p.7)

import Mathlib
import Definitions.Def_GlobalSinkhorn_s2
import Definitions.Def_GlobalSinkhorn_rowNormalize
import Definitions.Def_GlobalSinkhorn_skIter
import Definitions.Def_GlobalSinkhorn_marginalErr
import Definitions.Def_GlobalSinkhorn_Supplement_IsDense
import Definitions.Def_GlobalSinkhorn_Supplement_normalizedMatrix

open Matrix

namespace GlobalSinkhorn.Supplement

/-- Theorem 1.7 (Sinkhorn–Knopp on dense inputs).
He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), Theorem 1.7, pp.8–9.

Fix `γ, ρ ∈ (0, 1]`. For all sufficiently large `n`, let `D ∈ [0,1]^{n×n}` be `(γ, ρ)`-dense,
with row sums `r`, column sums `c`, `E = diag(r)^{-1/2} D diag(c)^{-1/2}` and `σ = s₂(E)`.
(a) If `σ < γρ − τ` for a positive constant `τ`, SK achieves the error `ε` in
`O_{ρ,γ,τ}(log n + log 1/ε)` iterations. (b) If `γ > 1/2`, SK achieves the error `ε` in
`O_{ρ,γ}(log n + log 1/ε)` iterations.

**Formalization Note.** "Sufficiently large `n`" is `∃ N` depending only on `γ, ρ` (chosen
before `τ`, as on the page). The SK input is the row-normalized `A = diag(r)⁻¹ D`
(`rowNormalize D`; p.7 "first normalize its rows", proof p.63); `D` has positive row sums by
density, so the total division never fires. One normalization is one iteration (`skIter`),
"achieves the error `ε` in `k` iterations" is: some iterate `t ≤ k` has total marginal
`ℓ₁` error (14) at most `ε`. The `O`-constant `C` depends on `(γ, ρ, τ)` in (a) and on
`(γ, ρ)` in (b); `ε` ranges over `(0, 1]`. `E` is `normalizedMatrix D`. -/
theorem theorem_1_7 :
    ∀ γ ρ : ℝ, 0 < γ → γ ≤ 1 → 0 < ρ → ρ ≤ 1 →
    ∃ N : ℕ,
      (∀ τ : ℝ, 0 < τ → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, N ≤ n → ∀ D : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, 0 ≤ D i j ∧ D i j ≤ 1) → IsDense γ ρ D →
          s2 (normalizedMatrix D) < γ * ρ - τ →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∃ t : ℕ, (t : ℝ) ≤ C * (Real.log n + Real.log (1 / ε)) ∧
              marginalErr (skIter (rowNormalize D) t) ≤ ε) ∧
      (1 / 2 < γ → ∃ C : ℝ, 0 < C ∧
        ∀ n : ℕ, N ≤ n → ∀ D : Matrix (Fin n) (Fin n) ℝ,
          (∀ i j, 0 ≤ D i j ∧ D i j ≤ 1) → IsDense γ ρ D →
          ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
            ∃ t : ℕ, (t : ℝ) ≤ C * (Real.log n + Real.log (1 / ε)) ∧
              marginalErr (skIter (rowNormalize D) t) ≤ ε) := by sorry

end GlobalSinkhorn.Supplement
