-- Prove2me | Theorems.Thm_LCAntiConc_lemma_4_3
-- name    : LCAntiConc.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:51:22.198306+00:00
-- url     : https://prove2.me/theorems/3cb6ea42-6d63-461e-884f-5090f6c4fd8e
-- title:
--   Lemma 4.3 — interpolation error
-- statement:
--   Let $A_1,A_2,A_3>0$. There is a constant $C>0$ such that the following holds. Let $\delta>0$, $k\ge3$, and let $X\in\mathbb R^d$ be a random vector that is $\delta$-strengthened anti-concentrated at degree $k$ (Definition 4.1, constant $A_3$) with polynomial $q$, and that has a $(T,\delta^4)$-bounded approximate Stein kernel $(H,r)$ (Definition B.1, constant $A_2$ in (B.3)) with $T\le A_1\log(1/\delta)$. Let $\tilde{\mathbb E}$ be any degree-$2k$ pseudo-expectation satisfying $\{\|v\|^2=1\}$, and let $\mu=\tilde{\mathbb E}v$, $\Sigma=\tilde{\mathbb E}(\mu-v)(\mu-v)^\top$, $\sigma^2=\operatorname{Tr}\Sigma$, and $G\sim N(0,1)$ independent of $X$. Then
--
--   $$\Big|\tilde{\mathbb E}\,\mathop{\mathbb E}_X q(\langle X,v\rangle)-\mathop{\mathbb E}_{X,G}q(\langle X,\mu\rangle+\sigma G)\Big|\le C\,\delta^{-2}\log(1/\delta)\Big(\sqrt{\mathop{\mathbb E}_X\mathrm{Var}_{\tilde{\mathbb E}}\,v^\top Hv}+\|\Sigma\|_{\mathrm{op}}^{1/4}\Big)+C\,\delta .$$
--
--   The lemma compares the pseudo-expectation with an actual one-dimensional Gaussian-smoothed marginal; the error is controlled by the pseudo-variance of $v^\top Hv$ and the size of the pseudo-covariance, which Lemma 4.4 makes small.
--
--   Differences from the source:
--   - reading: O(·) inside the hypotheses ((O(log 1/δ), δ⁴)-kernel, the O(δ) and O(δ^{-2r}) of Definition 4.1, the O(·) of (B.3)) → universally quantified parameters A₁, A₂, A₃ > 0; the conclusion's constants depend only on them; reason: an O(·) in a hypothesis fixes a class with some constant; the conclusion must hold for each such class
--   - reading: "… = O(δ⁻² log 1/δ)·(…) + O(δ)" for a signed difference → |difference| ≤ C δ⁻² log(1/δ)(…) + C δ; reason: the standard meaning of = O(·); the proof bounds absolute values
--   - reading: "degree-m polynomial" in Definition 4.1 → deg q ≤ m; reason: Lemmas 4.12–4.13 say "for some m ≤ …" and Theorem 4.2 uses m only through D = O(m + δ^{-30}); ≤ is the reading under which the chain fits
--   - encoding: random vector X ∈ ℝ^d → its law μ, a probability measure on EuclideanSpace ℝ (Fin d); reason: Euclidean norm and inner product; same instances
--   - encoding: a degree-D pseudo-expectation, a linear functional on ℝ[v]_{≤D} → a linear functional on all of ℝ[v] constrained only on polynomials of degree ≤ D; reason: its restriction to ℝ[v]_{≤D} is the page's object; the statement applies it only to polynomials of degree ≤ D
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.3, p.18 (PDF p.20); restated p.19 (PDF p.21)

import Mathlib
import Definitions.Def_LCAntiConc_IsPseudoExp
import Definitions.Def_LCAntiConc_IsStrengthenedAC
import Definitions.Def_LCAntiConc_IsStein
import Definitions.Def_LCAntiConc_expectQ
import Definitions.Def_LCAntiConc_pMean
import Definitions.Def_LCAntiConc_pCov
import Definitions.Def_LCAntiConc_pVar
import Definitions.Def_LCAntiConc_quadForm
import Definitions.Def_LiqPremiaEq_opNorm

namespace LCAntiConc

open MeasureTheory ProbabilityTheory

/-- **Lemma 4.3** (Interpolation Error). Let `k ≥ 3`. Let `X ∈ ℝ^d` be `δ`-strengthened
anti-concentrated at degree `k` with polynomial `q`, with an `(O(log 1/δ), δ⁴)`-approximate Stein
kernel `(H, r)`. Let `Ẽ` be any degree-`2k` pseudo-expectation satisfying `{‖v‖² = 1}`, and let
`μ = Ẽ v`, `Σ = Ẽ(μ - v)(μ - v)ᵀ`, `σ² = Tr Σ`, `G ∼ N(0, 1)` independent of `X`. Then
`Ẽ 𝔼_X q(⟨X, v⟩) - 𝔼_{X,G} q(⟨X, μ⟩ + σG) = O(δ⁻² log 1/δ)·(√(𝔼_X Var_Ẽ vᵀHv) + ‖Σ‖_op^{1/4}) + O(δ)`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.3, p.18 (PDF p.20); restated p.19 (PDF p.21).

**Formalization Note** The constants inside the hypotheses are parameters: `A₁` in
`T ≤ A₁ log(1/δ)`, `A₂` in (B.3), `A₃` in Definition 4.1. The conclusion's constant `C`
depends only on them and comes before `δ, k, d`, the law, `q`, the kernel and `Ẽ`. As on the page,
no smallness of `δ` is assumed (the hypotheses force `log(1/δ) ≥ 1/A₁`, since `T ≥ 1`).
"`= O(·)`" is read two-sided (`|·| ≤`). The law
`μ` of `X` is a probability measure; the pseudo-mean is `c = pMean Ẽ` (the page's `μ`), and
`(X, G)` has law `μ ⊗ N(0, 1)`. -/
theorem lemma_4_3 (A₁ A₂ A₃ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂) (hA₃ : 0 < A₃) :
    ∃ C > 0, ∀ δ : ℝ, 0 < δ → ∀ k : ℕ, 3 ≤ k →
      ∀ (d : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
        (q : Polynomial ℝ) (T : ℝ) (H : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
        (r : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)),
      IsStrengthenedAC μ δ k A₃ q → T ≤ A₁ * Real.log (1 / δ) → IsStein μ T (δ ^ 4) A₂ H r →
      ∀ L : MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ, IsPseudoExp (2 * k) L →
        |L (expectQ μ q) -
            ∫ p : EuclideanSpace ℝ (Fin d) × ℝ,
              q.eval (∑ i, p.1 i * pMean L i + Real.sqrt (pCov L).trace * p.2)
                ∂(μ.prod (gaussianReal 0 1))| ≤
          C * δ ^ (-2 : ℤ) * Real.log (1 / δ) *
              (Real.sqrt (∫ x, pVar L (quadForm (H x)) ∂μ) +
                LiqPremiaEq.opNorm (pCov L) ^ (1 / 4 : ℝ)) + C * δ := by sorry

end LCAntiConc
