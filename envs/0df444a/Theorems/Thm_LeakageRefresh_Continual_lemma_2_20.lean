-- Prove2me | Theorems.Thm_LeakageRefresh_Continual_lemma_2_20
-- name    : LeakageRefresh.Continual.lemma_2_20
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T23:09:05.211016+00:00
-- url     : https://prove2.me/theorems/3e58f126-007e-4ee9-9bdb-c8d365379576
-- title:
--   Lemma 2.20 — two-secret discrepancy: $|\mathbb E_{\mu_0}F-\mathbb E_{\mu_1}F|\le 3(N-2)^{-1/2}\|F\|_*$
-- statement:
--   Let $n\ge2$ and $N=2^n$. For every real table $F$ on $U_L\times U_R$,
--   $$\Big|\mathbb E_{(\ell,r)\leftarrow\mu_0}[F(\ell,r)]-\mathbb E_{(\ell,r)\leftarrow\mu_1}[F(\ell,r)]\Big|\le\frac{3}{\sqrt{N-2}}\,\|F\|_*. \tag{2.14}$$
--   In particular, for real functions $u:U_L\to\mathbb R$ and $v:U_R\to\mathbb R$,
--   $$\Big|\mathbb E_{\mu_0}[u(\ell)v(r)]-\mathbb E_{\mu_1}[u(\ell)v(r)]\Big|\le\frac{3}{\sqrt{N-2}}\,\|u\|_2\|v\|_2. \tag{2.15}$$
--   This is the extractor property of the inner product, used to change the bit encoded by one state in the hybrid argument.
--
--   Differences from the source:
--   - encoding: $\mathbb E_{(\ell,r)\leftarrow\mu_s}[\cdot]$ → finite sums weighted by the point probabilities `mu n s`; reason: expectations over finite distributions written as weighted sums
-- source:
--   Dziembowski, Faust, Leakage-Resilient Computation via Matrix Refreshing, arXiv:2611.04876 (sha256 fdbb2454…), p. 23, Lemma 2.20

import Mathlib
import Definitions.Def_LeakageRefresh_Continual_Encoding
import Definitions.Def_LeakageRefresh_Continual_Tables

namespace LeakageRefresh.Continual

/-- **Lemma 2.20 (Two-secret discrepancy).** With `N = 2ⁿ`: (2.14) for every real table `F` on
`U_L × U_R`, `|E_{µ₀}[F] − E_{µ₁}[F]| ≤ 3/√(N − 2) · ‖F‖_*`; (2.15) for `u : U_L → ℝ`,
`v : U_R → ℝ`, `|E_{µ₀}[u(ℓ) v(r)] − E_{µ₁}[u(ℓ) v(r)]| ≤ 3/√(N − 2) · ‖u‖₂ ‖v‖₂`. -/
theorem lemma_2_20 (n : ℕ) (hn : 2 ≤ n) :
    (∀ F : Table (UL n) (UR n),
      |muExp n 0 (fun x => F x.1 x.2) - muExp n 1 (fun x => F x.1 x.2)| ≤
        3 / Real.sqrt ((2 : ℝ) ^ n - 2) * nuclearNorm F) ∧
    (∀ (u : UL n → ℝ) (v : UR n → ℝ),
      |muExp n 0 (fun x => u x.1 * v x.2) - muExp n 1 (fun x => u x.1 * v x.2)| ≤
        3 / Real.sqrt ((2 : ℝ) ^ n - 2) * l2 u * l2 v) := by sorry

end LeakageRefresh.Continual
