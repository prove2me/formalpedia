-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_6
-- name    : LCAntiConc.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:44.776199+00:00
-- url     : https://prove2.me/theorems/18128daa-f536-4675-b885-50916546068a
-- title:
--   Lemma 4.6 — pseudo-variance conditioning: $\mathbb E_{\mathcal C}\mathbb E_X\mathrm{Var}_{\tilde{\mathbb E}_i}v^\top Hv\le6K^2/k$
-- statement:
--   Let $k\ge1$ be an integer, $K\in\mathbb R$, and let $H\in\mathbb R^{d\times d}$ be a random matrix with $\|H\|_{\mathrm{op}}\le K$ with probability $1$. For every pseudo-expectation $\tilde{\mathbb E}$ satisfying $\{\|v\|^2=1\}$ of degree $D\ge10k$ there is a degree-$6k$ partition $\mathcal C=\{(p_i,\tilde{\mathbb E}_i)\}$ of $\tilde{\mathbb E}$ with
--
--   $$\mathop{\mathbb E}_{\mathcal C}\mathop{\mathbb E}_X\mathrm{Var}_{\tilde{\mathbb E}_i}\big(v^\top Hv\big)\le\frac{6K^2}{k}.$$
--
--   $H$ need not be symmetric. This is the pseudo-variance half of Lemma 4.4.
--
--   Differences from the source:
--   - generalization: random H = H(X) for X ∈ ℝ^d → H a measurable random matrix on an arbitrary probability space (Ω, P); reason: specializes to Ω = ℝ^d with the law of X; the proof uses only expectations over the randomness of H
--   - encoding: random matrix → entrywise measurable map; reason: a random variable is measurable; Matrix carries no measurable-space instance in Mathlib
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.6, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_IsPartition
import Definitions.Def_LCAntiConc_pVar
import Definitions.Def_LCAntiConc_quadForm
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory

/-- **Lemma 4.6** (Pseudo-Variance Conditioning). Let `k ≥ 1` be an integer, `K ∈ ℝ` fixed, and
`H ∈ ℝ^{d×d}` a random matrix with `‖H‖_op ≤ K` with probability 1. For any pseudo-expectation
`Ẽ` satisfying `{‖v‖² = 1}` of degree at least `10k`, there is a degree-`6k` partition
`𝒞 = {(pᵢ, Ẽᵢ)}` with `𝔼_𝒞 𝔼_X Var_{Ẽᵢ} vᵀHv ≤ 6K²/k`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.6, p.21 (PDF p.23).

**Formalization Note** The randomness of `H` (written `H = H(X)`, `X ∈ ℝ^d`) is an arbitrary
probability space `(Ω, P)`, and `H` is measurable entrywise. `H` need not be symmetric. -/
theorem lemma_4_6 (d k : ℕ) (hk : 1 ≤ k) (K : ℝ) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (H : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hH : ∀ i j, Measurable fun ω => H ω i j) (hK : ∀ᵐ ω ∂P, LiqPremiaEq.opNorm (H ω) ≤ K)
    (D : ℕ) (hD : 10 * k ≤ D) (L : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ) (hL : IsPseudoExp D L) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℝ) (Li : ι → MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ),
      IsPartition D (6 * k) L p Li ∧
      ∑ i, p i * ∫ ω, pVar (Li i) (quadForm (H ω)) ∂P ≤ 6 * K ^ 2 / k := by sorry

end LCAntiConc
