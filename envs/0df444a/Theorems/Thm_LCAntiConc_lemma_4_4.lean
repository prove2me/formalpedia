-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_4
-- name    : LCAntiConc.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:58.464283+00:00
-- url     : https://prove2.me/theorems/0f2887a6-4cc1-4f2b-bdb8-1f1b6b073151
-- title:
--   Lemma 4.4 — one degree-$8k$ partition with small pseudo-variance and small pseudo-covariance
-- statement:
--   Let $K\in\mathbb R$, let $k\ge1$ be an integer, and let $H\in\mathbb R^{d\times d}$ be a random matrix with $\|H\|_{\mathrm{op}}\le K$ with probability $1$. For every pseudo-expectation $\tilde{\mathbb E}$ satisfying $\{\|v\|^2=1\}$ of degree $D\ge10k+2$ there is a degree-$8k$ partition $\mathcal C=\{(p_i,\tilde{\mathbb E}_i)\}$ of $\tilde{\mathbb E}$ such that
--
--   $$\mathop{\mathbb E}_{\mathcal C}\mathop{\mathbb E}_X\mathrm{Var}_{\tilde{\mathbb E}_i}\big(v^\top Hv\big)\le\frac{6K^2}{k},\qquad \mathop{\mathbb E}_{\mathcal C}\|\Sigma_i\|_{\mathrm{op}}\le\frac1{\sqrt k},$$
--
--   where $\Sigma_i=\tilde{\mathbb E}_i(v-\mu_i)(v-\mu_i)^\top$ and $\mu_i=\tilde{\mathbb E}_iv$.
--
--   Theorem 4.2 applies this with $K=O(\log1/\delta)$ to make the interpolation error of Lemma 4.3 small.
--
--   Differences from the source:
--   - generalization: random H = H(X) for X ∈ ℝ^d → H a measurable random matrix on an arbitrary probability space (Ω, P); reason: specializes to Ω = ℝ^d with the law of X; the proof uses only expectations over the randomness of H
--   - encoding: random matrix → entrywise measurable map; reason: a random variable is measurable; Matrix carries no measurable-space instance in Mathlib
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.4, p.18 (PDF p.20); restated p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_IsPartition
import Definitions.Def_LCAntiConc_pVar
import Definitions.Def_LCAntiConc_pCov
import Definitions.Def_LCAntiConc_quadForm
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.4**. Let `K ∈ ℝ` be fixed and `k ≥ 1` an integer, and let `H ∈ ℝ^{d×d}` be a random
matrix with `‖H‖_op ≤ K` with probability 1. For any pseudo-expectation `Ẽ` satisfying
`{‖v‖² = 1}` of degree at least `10k + 2`, there is a degree-`8k` partition `𝒞 = {(pᵢ, Ẽᵢ)}`
with `𝔼_𝒞 𝔼_X Var_{Ẽᵢ} vᵀHv ≤ 6K²/k` and `𝔼_𝒞 ‖Σᵢ‖_op ≤ 1/√k`, where
`Σᵢ = Ẽᵢ(v - μᵢ)(v - μᵢ)ᵀ`, `μᵢ = Ẽᵢ v`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.4, p.18 (PDF p.20); restated p.21 (PDF p.23).

**Formalization Note** The randomness of `H` is an arbitrary probability space `(Ω, P)`, and `H`
is measurable entrywise. One partition satisfies both bounds. -/
theorem lemma_4_4 (d k : ℕ) (hk : 1 ≤ k) (K : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ i j, Measurable fun ω => H ω i j) (hK : ∀ᵐ ω ∂P, LiqPremiaEq.opNorm (H ω) ≤ K)
    (D : ℕ) (hD : 10 * k + 2 ≤ D) (L : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ) (hL : IsPseudoExp D L) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (Li : ι → MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ),
      IsPartition D (8 * k) L p Li ∧
      ∑ i, p i * ∫ ω, pVar (Li i) (quadForm (H ω)) ∂P ≤ 6 * K ^ 2 / k ∧
      ∑ i, p i * LiqPremiaEq.opNorm (pCov (Li i)) ≤ 1 / Real.sqrt k := by sorry

end LCAntiConc
