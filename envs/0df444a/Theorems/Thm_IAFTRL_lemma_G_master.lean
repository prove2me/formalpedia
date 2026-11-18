-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_master
-- name    : IAFTRL.lemma_G_master
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:46:53.610367+00:00
-- url     : https://prove2.me/theorems/2e330e5b-7bcc-4ce3-81c8-ecb0ee53e2ca
-- title:
--   Master decomposition (G.3)–(G.5) of the GIA-FTRL regret against an atom
-- statement:
--   **Setting.** A GIA-FTRL run of $T\ge1$ rounds against an adaptive environment, any vector $\theta$, and any atom $a^*$ of the reference measure $\mu$, with $h^*=\log(1/\mu(\{a^*\}))$.
--
--   **Claim.**
--   $$\mathrm{Reg}_T(a^*)\le I_1+I_2+I_3+I_4 .$$
--   Here $I_1=\beta_1h^*+\sum_{t\ge2}(\beta_t-\beta_{t-1})\mathbb E[h^*-D_{\mathrm{KL}}(q_t,\mu)]$, $I_2=\sum_t\mathbb E[D_t]$, $I_3=\sum_t\mathbb E\langle p_t-q_t,\Delta\rangle$, and $I_4=\sum_t\mathbb E\langle p_t-q_t,x^\top c^{\mathrm{vec}}_t\rangle$.
--
--   **Proof idea.**
--   1. Unbiased loss differences give $\mathrm{Reg}_T(a^*)=\mathbb E\sum_t\langle q_t-\delta_{a^*},\hat\ell_t\rangle+\mathbb E\sum_t\langle p_t-q_t,x^\top\theta_t\rangle$.
--   2. The localized entropy identity (J.5) bounds the first sum by $I_1+I_2$.
--   3. The second sum splits as $\theta_t=\theta+c^{\mathrm{vec}}_t$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.1.1, (G.3)–(G.5), and Lemma J.2 (J.5)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms

namespace IAFTRL

open MeasureTheory

/-- **The master decomposition (G.3)–(G.5) with the localized entropy identity (J.5).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version),
proof of Proposition G.1, pp.123–124: "`Reg_T(a*) = E[Σ_t ⟨q_t − δ_a*, ℓ̂_t⟩] + E[Σ_t ⟨p_t − q_t, Δ⟩] +
E[Σ_t ⟨p_t − q_t, xᵀc_t⟩] ≤ β₁h* + Σ_{t=2}^T (β_t − β_{t−1}) E[h* − D_KL(q_t, µ)] + Σ_t E[D_t] + …`"
(Lemma J.2, (J.5)).

For every execution of GIA-FTRL for `T ≥ 1` rounds, every vector `θ` and every atom `a*` of the
reference measure (`µ({a*}) > 0`, `h* = log(1/µ({a*}))`):
`Reg_T(a*) ≤ I₁ + I₂ + I₃ + I₄` with the sums of `IAFTRL_GTerms`. -/
theorem lemma_G_master {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℕ)
    (R : GRun d Ω) (hT : 1 ≤ T) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R) (θ astar : Fin d → ℝ)
    (hatom : 0 < refMu ℬ e {astar}) :
    gRegretVs P T R astar ≤ penI1 P ℬ e T R astar + stabI2 P ℬ e T R +
      exploI3 P ℬ e T R θ astar + corrI4 P ℬ e T R θ := by sorry

end IAFTRL
