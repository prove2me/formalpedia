-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_9
-- name    : IAFTRL.lemma_G_9
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:46:53.714975+00:00
-- url     : https://prove2.me/theorems/4615a1d8-cb59-4544-89e2-868c3e9ad1c6
-- title:
--   Lemma G.9 — direct corruption contribution of GIA-FTRL
-- statement:
--   **Setting.** A GIA-FTRL run of $T\ge1$ rounds in the corrupted regime with budget $C\ge0$: $\|\theta\|_{\mathcal A}\le1$, $\|\theta_t\|_{\mathcal A}\le1$, and $\sum_t\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely.
--
--   **Claim.**
--   $$I_4=\sum_t\mathbb E\langle p_t-q_t,x^\top c^{\mathrm{vec}}_t\rangle\le32\,d\sqrt C .$$
--   The paper states the slightly smaller constant $16\sqrt2\,d$.
--
--   **Proof idea.**
--   1. Marginal domination gives $p_t-q_t=\Gamma_t(\tilde p_t-q_t)$ for a probability measure $\tilde p_t$.
--   2. On $\mathcal K$ the range of $x^\top c^{\mathrm{vec}}_t$ is at most $2\kappa_t$, where $\kappa_t=\|c^{\mathrm{vec}}_t\|_{\mathcal A}\le2$.
--   3. With $\Gamma_t\le4d/\sqrt t$, it remains to show $\sum_t\kappa_t/\sqrt t\le4\sqrt C$. Split at $m=\lfloor C/4\rfloor$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.5, Lemma G.9, (G.148)–(G.151)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.9 (Direct corruption contribution).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.9, p.137: "For
`κ_t = ‖c_t^vec‖_𝒜` with `0 ≤ κ_t ≤ 2` and `Σ_t κ_t ≤ C` almost surely,
`I₄ := Σ_t E[⟨p_t − q_t, xᵀc_t^vec⟩] ≤ 16√2 d √C`."

Stated with the slightly larger constant `32 d`: for every GIA-FTRL run of `T ≥ 1` rounds in the
corrupted regime with budget `C ≥ 0`, `I₄ ≤ 32 d √C`. -/
theorem lemma_G_9 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (θ : Fin d → ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℕ) (C : ℝ) (R : GRun d Ω) (hT : 1 ≤ T) (hC : 0 ≤ C) (hR : IsGIAFTRLRun P 𝒜 ℬ e T R)
    (hcor : IsCorruptedG P 𝒜 θ C T R) :
    corrI4 P ℬ e T R θ ≤ 32 * d * Real.sqrt C := by sorry

end IAFTRL
