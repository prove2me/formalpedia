-- Prove2me | Theorems.Thm_MatrixAnalytic_LogReduction_products_first_passage
-- name    : MatrixAnalytic.LogReduction.products_first_passage
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:01.677514+00:00
-- url     : https://prove2.me/theorems/3aacfae7-00c6-4739-8e1a-5fbf0255476e
-- title:
--   Eqs. (8.47)–(8.48) — the products Π H^[i] and (Π H^[i]) L^[k] as first passage probabilities from ℓ(1)
-- statement:
--   Let $\{X_t\}$ be an irreducible homogeneous QBD with transition matrix (8.1), and $H^{[i]}, L^{[k]}$ the matrices of the logarithmic reduction recursion (8.40)–(8.44) (inverses read as $\sum_\nu M^\nu$). For every $k\ge0$,
--   $$\prod_{0\le i\le k}H^{[i]}=\mathrm P[\delta(k+1)<\gamma(0)\ \&\ X_{\delta(k+1)}\mid X_0\in\ell(1)]$$
--   and
--   $$\Big(\prod_{0\le i\le k-1}H^{[i]}\Big)L^{[k]}=\mathrm P[\delta(k)<\gamma(0)<\delta(k+1)\ \&\ X_{\gamma(0)}\mid X_0\in\ell(1)],$$
--   where $\prod_{0\le i\le k}H^{[i]}=H^{[0]}H^{[1]}\cdots H^{[k]}$, the empty product is the identity, $\gamma(0)$ is the first passage time to $\ell(0)$ and $\delta(k)$ that to $\ell(2^k)$. The first matrix records, from $(1,i)$, the probability of reaching $\ell(2^{k+1})$ before $\ell(0)$, in phase $j$; the second the probability of visiting $\ell(2^k)$ and then reaching $\ell(0)$, in phase $j$, before $\ell(2^{k+1})$.
--
--   This is the second step of the proof of Theorem 8.4.1: combined with (8.37) it gives the series (8.39).
--
--   **Formalization Note** Products of matrices and the inverses of the recursion are computed in $[0,\infty]$, inverses as $\sum_\nu M^\nu$; probabilities are sums over finite trajectories.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 192, Eqs. (8.47)–(8.48)

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction

/-- Eqs. (8.47)–(8.48), p. 192. For an irreducible QBD (8.1) and every `k ≥ 0`, with `H^{[i]}`,
`L^{[k]}` the matrices of the recursion (8.40)–(8.44) and `Π_{0≤i≤k} H^{[i]}` the ordered product
`H^{[0]} ⋯ H^{[k]}`:
`Π_{0≤i≤k} H^{[i]} = P[δ(k+1) < γ(0) & X_{δ(k+1)} | X₀ ∈ ℓ(1)]` (8.47) and
`(Π_{0≤i≤k−1} H^{[i]}) L^{[k]} = P[δ(k) < γ(0) < δ(k+1) & X_{γ(0)} | X₀ ∈ ℓ(1)]` (8.48).
Products are computed in `ℝ≥0∞`. -/
theorem products_first_passage {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ∀ k : ℕ,
      prodH A₀ A₁ A₂ (k + 1) = hitUpFromOne (qbdP B A₀ A₁ A₂) k ∧
      matMulE (prodH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) =
        hitDownInBand (qbdP B A₀ A₁ A₂) k := by sorry

end MatrixAnalytic.LogReduction
