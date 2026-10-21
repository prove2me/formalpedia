-- Prove2me | Theorems.Thm_MatrixAnalytic_LogReduction_G_log_reduction_series
-- name    : MatrixAnalytic.LogReduction.G_log_reduction_series
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:09.172774+00:00
-- url     : https://prove2.me/theorems/e7652fbb-3b21-4dfb-acf0-eb948ead7cb3
-- title:
--   Theorem 8.4.1 — the logarithmic reduction series G = Σ_k (Π_{i<k} H^[i]) L^[k]
-- statement:
--   Let $\{X_t\}$ be an irreducible homogeneous discrete-time QBD with transition matrix (8.1), blocks $B, A_0, A_1, A_2$ and phases $\iota$ (finitely or countably many), and let $G$ be its matrix of first passage probabilities from $\ell(1)$ to $\ell(0)$: $G_{ij}=\mathrm P[\gamma(0)<\infty\ \&\ X_{\gamma(0)}=(0,j)\mid X_0=(1,i)]$. Define
--   $$H^{[0]}=(I-A_1)^{-1}A_0,\qquad L^{[0]}=(I-A_1)^{-1}A_2,$$
--   $$H^{[k+1]}=(I-U^{[k]})^{-1}(H^{[k]})^2,\qquad L^{[k+1]}=(I-U^{[k]})^{-1}(L^{[k]})^2\qquad(k\ge0),$$
--   with $U^{[k]}=H^{[k]}L^{[k]}+L^{[k]}H^{[k]}$. Then every inverse in this recursion is finite (each entry of $\sum_\nu A_1^\nu$ and of $\sum_\nu(U^{[k]})^\nu$ is finite), and
--   $$G=\sum_{k\ge0}\Big(\prod_{0\le i\le k-1}H^{[i]}\Big)L^{[k]},$$
--   where $\prod_{0\le i\le k-1}H^{[i]}=H^{[0]}\cdots H^{[k-1]}$ and the empty product ($k=0$) is the identity.
--
--   The partial sums of this series are the iterates of the logarithmic reduction algorithm (Figure 8.6), which converges quadratically; the theorem says that a recursion involving only the blocks $A_0, A_1, A_2$ produces the first passage matrix $G$ defined by the dynamics of the chain.
--
--   **Formalization Note** $G$ is defined probabilistically, as a sum over finite trajectories of products of one-step transition probabilities, not as a solution of a matrix equation. The inverses are the book's convention $(I-M)^{-1}:=\sum_{\nu\ge0}M^\nu$ (p. 109), computed entrywise in $[0,\infty]$; their finiteness is part of the conclusion. Products and the series are computed in $[0,\infty]$, entrywise.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, pp. 190–191, Theorem 8.4.1

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction

/-- Theorem 8.4.1, pp. 190–191. For an irreducible QBD (8.1), the first-passage matrix `G` (8.3)
from `ℓ(1)` to `ℓ(0)`, `G_{ij} = P[γ(0) < ∞ & X_{γ(0)} = (0, j) | X₀ = (1, i)]` (a sum over finite
trajectories of products of one-step transition probabilities, in `ℝ≥0∞`), is given by `G = Σ_{k≥0} (Π_{0≤i≤k−1} H^{[i]}) L^{[k]}` (8.39), where `H^{[0]} = (I − A₁)⁻¹A₀`,
`L^{[0]} = (I − A₁)⁻¹A₂`, `H^{[k+1]} = (I − U^{[k]})⁻¹(H^{[k]})²`,
`L^{[k+1]} = (I − U^{[k]})⁻¹(L^{[k]})²` and `U^{[k]} = H^{[k]}L^{[k]} + L^{[k]}H^{[k]}`
(8.40)–(8.44), the ordered product `Π_{0≤i≤k−1} H^{[i]} = H^{[0]} ⋯ H^{[k−1]}` being the identity
for `k = 0`. Every inverse is `(I − M)⁻¹ := Σ_{ν≥0} M^ν`, and the conclusion includes that each
of these series has finite entries; products and the series (8.39) are computed in `ℝ≥0∞`. -/
theorem G_log_reduction_series {ι : Type*} [Countable ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    (∀ i j : ι, seriesInvE (ennMat A₁) i j ≠ ⊤) ∧
    (∀ k : ℕ, ∀ i j : ι, seriesInvE (logU A₀ A₁ A₂ k) i j ≠ ⊤) ∧
    ∀ i j : ι, matG (qbdP B A₀ A₁ A₂) i j =
      ∑' k : ℕ, matMulE (prodH A₀ A₁ A₂ k) (logL A₀ A₁ A₂ k) i j := by sorry

end MatrixAnalytic.LogReduction
