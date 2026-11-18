-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_2_ftrl
-- name    : IAFTRL.lemma_G_2_ftrl
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T12:00:47.332526+00:00
-- url     : https://prove2.me/theorems/c6de17a4-33f6-4773-979e-7e5ff48e8150
-- title:
--   All-history FTRL bound of GIA-FTRL against a comparison law (G.218)–(G.241)
-- statement:
--   **Setting.** As in Proposition G.2: a GIA-FTRL run of $T\ge1$ rounds on a compact generator $\mathcal B$ of $\mathcal A\subseteq\mathbb B^d$, against an adaptive environment. Write $\beta_t=16d+\sqrt t$ and let $\mu$ be the reference measure (3.3).
--
--   **Claim.** Let $u\in\mathcal K=\mathrm{Conv}(\mathcal B)$. Let $q$ be a probability measure supported on $\mathcal K$ with $q\ll\mu$ and integrable log-density. Let $\varepsilon\ge0$ satisfy $|(\int x\,q(dx)-u)^\top\vartheta|\le\varepsilon$ for every $\|\vartheta\|_{\mathcal A}\le1$. Then
--   $$\mathrm{Reg}_T(u)\le\beta_T\,D_{\mathrm{KL}}(q,\mu)+\sum_{t=1}^T\frac{10d}{\beta_t}+T\varepsilon .$$
--
--   **Proof outline** ((G.218)–(G.241)).
--   1. Telescope the potential $F_\beta(S)=-\beta\log\int e^{-x^\top S/\beta}\mu(dx)$. It is nondecreasing in $\beta$ and satisfies $F_\beta(S)\le\langle q,S\rangle+\beta D_{\mathrm{KL}}(q,\mu)$.
--   2. Bound the per-round term pathwise: $D_t\le\beta_t\int\chi(h_t)\,dq_t$.
--   3. Condition on the latent action: $\mathbb E_{t-1}[D_t]\le C_t(p_t)\le2d/\beta_t$.
--   4. Use marginal domination: $\langle p_t-q_t,x^\top\theta_t\rangle\le2\Gamma_t=8d/\beta_t$.
--   5. Use unbiased difference estimates.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6.3, proof of Proposition G.2, pp. 145–147

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **All-history FTRL bound against a comparison law (Proposition G.2, (G.218)–(G.241)).**
Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), proof of
Proposition G.2, pp.145–147: for a deterministic comparison law `q`,
`Reg_T(u) ≤ β_T D_KL(q, µ) + Σ_t E[D_t] + Σ_t 8d/β_t + Σ_t E[⟨q − δ_u, xᵀθ_t⟩]` (G.241), with
`E_{t−1}[D_t] ≤ C_t(p_t) ≤ 2d/β_t` (G.232).

For every execution of GIA-FTRL for `T ≥ 1` rounds, every comparator `u ∈ 𝒦`, every probability
measure `q` on `𝒦` with `q ≪ µ` and integrable log-density, and every `ε` with
`|(∫ x q(dx) − u)ᵀϑ| ≤ ε` whenever `‖ϑ‖_𝒜 ≤ 1`:
`Reg_T(u) ≤ β_T D_KL(q, µ) + Σ_{t=1}^T 10d/β_t + Tε`. -/
theorem lemma_G_2_ftrl {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (R : GRun d Ω) (hT : 1 ≤ T) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) (q : Measure (Fin d → ℝ)) [IsProbabilityMeasure q]
    (hqK : q (Kset ℬ)ᶜ = 0) (hqμ : q ≪ refMu ℬ e)
    (hKL : Integrable (fun x => Real.log (q.rnDeriv (refMu ℬ e) x).toReal) q) (ε : ℝ)
    (hε : ∀ ϑ : Fin d → ℝ, setNorm 𝒜 ϑ ≤ 1 → |((fun i => ∫ x, x i ∂q) - u) ⬝ᵥ ϑ| ≤ ε) :
    gRegretVs P T R u ≤ gbeta d T * ∫ x, Real.log (q.rnDeriv (refMu ℬ e) x).toReal ∂q +
      ∑ t ∈ Finset.range T, 10 * (d : ℝ) / gbeta d (t + 1) + T * ε := by sorry

end IAFTRL
