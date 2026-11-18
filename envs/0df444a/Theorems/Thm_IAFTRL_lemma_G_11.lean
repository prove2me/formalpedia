-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_11
-- name    : IAFTRL.lemma_G_11
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T12:00:59.272197+00:00
-- url     : https://prove2.me/theorems/7b16b3bd-7bfd-4338-9bc8-6bae5d61073b
-- title:
--   Lemma G.11 — comparison law of the convolution reference
-- statement:
--   **Setting.** Let $\mathcal A\subseteq\mathbb B^d$ be a compact spanning action set and $\mathcal B$ a compact generator of it, with $\mathcal K=\mathrm{Conv}(\mathcal B)$ of affine dimension $k\ge1$. Let $\mu=\sum_{j\in J}\pi_j\delta_{b_j}+\omega_\mu\mu_{16}$ be the reference measure (3.3) of GIA-FTRL. Here $\mu_{16}$ is the law of the mean of $16$ i.i.d. points drawn from the normalized $k$-dimensional Hausdorff measure on $\mathcal K$.
--
--   **Claim.** For every $u\in\mathcal K$ and every integer $T\ge1$ there is a probability measure $q_{u,T}$ supported on $\mathcal K$ with $q_{u,T}\ll\mu$ and
--   $$D_{\mathrm{KL}}(q_{u,T},\mu)=\int\log\frac{dq_{u,T}}{d\mu}\,dq_{u,T}\le\log2+16k\log T,$$
--   $$\Big|\Big(\int x\,q_{u,T}(dx)-u\Big)^{\!\top}\vartheta\Big|\le\frac2T\quad\text{for every }\|\vartheta\|_{\mathcal A}\le1 .$$
--   The log-density is integrable.
--
--   **Idea.** Pass to the shrunken copy $\mathcal K_\varepsilon=u+\varepsilon(\mathcal K-u)$ with $\varepsilon=1/T$. Its $k$-dimensional volume fraction is $\varepsilon^k$. Hence $\mu_{16}(\mathcal K_\varepsilon)\ge\varepsilon^{16k}$, and $\omega_\mu\ge1/2$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6.2, Lemma G.11, pp. 143–144

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.11 (Adversarial comparator cost of the convolution reference).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.11, p.143:
"For each `u ∈ 𝒦` and integer `T ≥ 1` there is a probability `q_{u,T}` such that
`D_KL(q_{u,T}, µ) ≤ log 2 + mk log T`, `|(∫ x q_{u,T}(dx) − u)ᵀϑ| ≤ 2/T` for every `‖ϑ‖_𝒜 ≤ 1`",
with `m = 16` and `µ` the reference measure (3.3).

`D_KL(q, µ)` is written as `∫ log (dq/dµ) dq`, with `q ≪ µ` and the log-density integrable; the
comparison law is supported on `𝒦 = Conv ℬ`. -/
theorem lemma_G_11 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) (T : ℕ) (hT : 1 ≤ T) :
    ∃ q : Measure (Fin d → ℝ), IsProbabilityMeasure q ∧ q (Kset ℬ)ᶜ = 0 ∧ q ≪ refMu ℬ e ∧
      Integrable (fun x => Real.log (q.rnDeriv (refMu ℬ e) x).toReal) q ∧
      ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q ≤
        Real.log 2 + 16 * (kdim ℬ : ℝ) * Real.log T ∧
      ∀ ϑ : Fin d → ℝ, setNorm 𝒜 ϑ ≤ 1 →
        |((fun i => ∫ x, x i ∂q) - u) ⬝ᵥ ϑ| ≤ 2 / T := by sorry

end IAFTRL
