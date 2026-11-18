-- Prove2me | Theorems.Thm_IAFTRL_proposition_G_2
-- name    : IAFTRL.proposition_G_2
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T09:15:59.554353+00:00
-- url     : https://prove2.me/theorems/8aff5202-f079-4471-bcde-4ea3f8004515
-- title:
--   Proposition G.2 — all-history adversarial guarantee of GIA-FTRL
-- statement:
--   **Setting.** Let $\mathcal A\subseteq\mathbb B^d$ ($d\ge1$) be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$.
--   - GIA-FTRL (Algorithm 2, definition `IAFTRL_GIAFTRL`) runs on a compact generator $\mathcal B$, meaning $\mathcal B\subseteq\mathcal A\subseteq\mathrm{Conv}(\mathcal B)$, with $k=\dim\mathrm{aff}\,\mathcal K\ge1$ for $\mathcal K=\mathrm{Conv}(\mathcal B)$, and with a surjective enumeration $e$ of $\mathbb Q^d$.
--   - The run lasts $T\ge1$ rounds against an adaptive environment: $\theta_t$ is predictable, $\|\theta_t\|_{\mathcal A}\le1$, $|Y_t|\le1$, and $\mathbb E[Y_t\mid\cdot]=A_t^\top\theta_t$.
--
--   **Claim.** For every comparator $u\in\mathcal K$,
--   $$\mathrm{Reg}_T(u)=\mathbb E\Big[\sum_{t<T}(A_t-u)^\top\theta_t\Big]\le 320(d+1)\sqrt T\,\log(eT).$$
--   No sharpness is assumed.
--
--   **Proof outline** (Appendix G.6.3).
--   1. Use the potential $F_\beta(S)=-\beta\log\int e^{-S/\beta}d\mu=\inf_q\{\langle q,S\rangle+\beta D_{\mathrm{KL}}(q,\mu)\}$ (Lemma J.2). It telescopes as in (G.218)–(G.225), with a deterministic comparison law $q_{u,T}$ satisfying $D_{\mathrm{KL}}(q_{u,T},\mu)\le\log2+16k\log T$ and $|(\int x\,dq_{u,T}-u)^\top\vartheta|\le2/T$ (Lemma G.11).
--   2. Bound the per-round term by $\mathbb E_{t-1}[D_t]\le C_t(p_t)\le2d/\beta_t$, using the proxy constraint (3.7) and Lemma J.4.
--   3. Bound the exploration term by $\langle p_t-q_t,x^\top\theta_t\rangle\le8d/\beta_t$, using marginal domination.
--   4. Use unbiasedness of the reconstruction.
--   5. Sum the schedule with $\beta_t=16d+\sqrt t$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6.3, Proposition G.2, pp. 145–147

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Proposition G.2 (All-history adversarial guarantee).** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits* (STOC submission version), Proposition G.2, p.145: "GIA-FTRL obeys
`Reg_T ≤ U_SH(T) ≤ 320(d+1)√T log(eT)` for every predictable bounded-mean environment."

For every execution of GIA-FTRL on a compact generator `ℬ` of the compact action set
`𝒜 ⊆ 𝔹^d` (`span 𝒜 = ℝ^d`, `k = dim aff 𝒦 ≥ 1`, `e` an enumeration of `ℚ^d`) for `T ≥ 1` rounds
against an adaptive environment, and every comparator `u ∈ 𝒦 = Conv ℬ`,
`Reg_T(u) ≤ 320(d+1)√T log(eT)`. No sharpness is assumed. -/
theorem proposition_G_2 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T : ℕ) (R : GRun d Ω) (hT : 1 ≤ T) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (u : Fin d → ℝ) (hu : u ∈ Kset ℬ) :
    gRegretVs P T R u ≤ 320 * ((d : ℝ) + 1) * Real.sqrt T * Real.log (Real.exp 1 * T) := by sorry

end IAFTRL
