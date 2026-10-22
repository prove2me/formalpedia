-- Prove2me | Theorems.Thm_MatrixAnalytic_LogReduction_G_band_decomposition
-- name    : MatrixAnalytic.LogReduction.G_band_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:10.666357+00:00
-- url     : https://prove2.me/theorems/76df0bde-eb56-44d4-9628-f043913237c6
-- title:
--   Eq. (8.37) — G = Σ_k P[δ(k) < γ(0) < δ(k+1) & X_γ(0) | X₀ ∈ ℓ(1)]
-- statement:
--   Let $\{X_t\}$ be an irreducible homogeneous QBD with transition matrix (8.1) and phases $\iota$ (finitely or countably many). Write $\gamma(0)=\inf\{t\ge1:X_t\in\ell(0)\}$ and $\delta(k)=\inf\{t\ge0:X_t\in\ell(2^k)\}$ for the first passage time to the level $2^k$ (8.38). Then the matrix $G$ of first passage probabilities from $\ell(1)$ to $\ell(0)$ decomposes according to the highest power of two reached before $\gamma(0)$:
--   $$G=\sum_{k\ge0}\mathrm P[\delta(k)<\gamma(0)<\delta(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(1)].$$
--   Here $G_{ij}=\mathrm P[\gamma(0)<\infty\ \&\ X_{\gamma(0)}=(0,j)\mid X_0=(1,i)]$, and the $k$-th term is the probability, starting from $(1,i)$, of visiting $\ell(2^k)$, then reaching $\ell(0)$, first at $(0,j)$, before any visit to $\ell(2^{k+1})$.
--
--   This decomposition is the probabilistic skeleton of the logarithmic reduction algorithm: Theorem 8.4.1 identifies the $k$-th term with $\big(\prod_{0\le i\le k-1}H^{[i]}\big)L^{[k]}$.
--
--   **Formalization Note** All probabilities are sums over finite trajectories of products of transition probabilities, with values in $[0,\infty]$, and the series is a sum in $[0,\infty]$, entrywise.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 190, Eq. (8.37)

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction

/-- Eq. (8.37), p. 190. For an irreducible QBD (8.1), the first-passage matrix `G` (8.3) from
`ℓ(1)` to `ℓ(0)` is the sum over `k ≥ 0` of the matrices
`P[δ(k) < γ(0) < δ(k+1) & X_{γ(0)} | X₀ ∈ ℓ(1)]`, where `δ(k)` is the first passage time to
the level `2^k` (8.38). Entrywise, in `ℝ≥0∞`. -/
theorem G_band_decomposition {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ i j : ι, matG (qbdP B A₀ A₁ A₂) i j =
      ∑' k : ℕ, hitDownInBand (qbdP B A₀ A₁ A₂) k i j := by sorry

end MatrixAnalytic.LogReduction
