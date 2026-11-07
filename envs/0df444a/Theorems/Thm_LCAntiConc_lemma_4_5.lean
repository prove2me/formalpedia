-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_5
-- name    : LCAntiConc.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:51.69463+00:00
-- url     : https://prove2.me/theorems/d274db47-6cc9-4b0f-8227-28b8a446aa7f
-- title:
--   Lemma 4.5 — spectral conditioning: $\mathbb E_{\mathcal C}\|\Sigma_{\tilde{\mathbb E}_i}\|_{\mathrm{op}}\le1/\sqrt k$
-- statement:
--   Let $k\ge1$ and let $\tilde{\mathbb E}$ be a degree-$2(k+1)$ pseudo-expectation satisfying $\{\|v\|^2=1\}$ over $\mathbb R^n$. Then there is a degree-$2k$ partition $\mathcal C=\{(p_i,\tilde{\mathbb E}_i)\}$ of $\tilde{\mathbb E}$ such that
--
--   $$\mathop{\mathbb E}_{\mathcal C}\big\|\Sigma_{\tilde{\mathbb E}_i}\big\|_{\mathrm{op}}=\sum_ip_i\,\big\|\Sigma_{\tilde{\mathbb E}_i}\big\|_{\mathrm{op}}\le\frac1{\sqrt k},$$
--
--   where $\Sigma_{\tilde{\mathbb E}_i}$ is the pseudo-covariance of $\tilde{\mathbb E}_i$ and $\|\cdot\|_{\mathrm{op}}$ the spectral norm.
--
--   Conditioning thus makes the pseudo-covariance small in operator norm on average, at a cost of $2k$ in degree; it is the spectral half of Lemma 4.4.
--
--   Differences from the source:
--   - encoding: k unrestricted → 1 ≤ k; reason: the bound 1/√k is undefined at k = 0 (Lean's 1/√0 = 0 would make that instance false); excludes only the undefined case
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.5, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_IsPartition
import Definitions.Def_LCAntiConc_pCov
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

/-- **Lemma 4.5** (Spectral Conditioning). Let `Ẽ` be a degree-`2(k+1)` pseudo-expectation
satisfying `{‖v‖² = 1}`. Then there is a degree-`2k` partition `𝒞 = {(pᵢ, Ẽᵢ)}` such that
`𝔼_𝒞 ‖Σ_{Ẽᵢ}‖_op ≤ 1/√k`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.5, p.21 (PDF p.23).

**Formalization Note** `k ≥ 1` is added: the bound `1/√k` is undefined at `k = 0`.
`Σ_{Ẽᵢ}` is the pseudo-covariance `pCov`, and `‖·‖_op` the `ℓ²` operator norm. -/
theorem lemma_4_5 (n k : ℕ) (hk : 1 ≤ k) (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hL : IsPseudoExp (2 * (k + 1)) L) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (Li : ι → MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ),
      IsPartition (2 * (k + 1)) (2 * k) L p Li ∧
      ∑ i, p i * LiqPremiaEq.opNorm (pCov (Li i)) ≤ 1 / Real.sqrt k := by sorry

end LCAntiConc
