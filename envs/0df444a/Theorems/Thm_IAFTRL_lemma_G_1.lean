-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_1
-- name    : IAFTRL.lemma_G_1
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:47:02.822425+00:00
-- url     : https://prove2.me/theorems/aa283316-1008-47bf-bdb1-22ec0235f199
-- title:
--   Lemma G.1 — relative-entropy penalty contribution of GIA-FTRL
-- statement:
--   **Setting.** The setting is that of Proposition G.1 (`proposition_G_1_anc`):
--   - a GIA-FTRL run on a compact generator $\mathcal B$ of a compact spanning $\mathcal A\subseteq\mathbb B^d$, with $k\ge1$;
--   - a sharp instance $(\theta,a^*)$ with $\|\theta\|_{\mathcal A}\le1$ and unique optimal action $a^*\in\mathcal A$;
--   - the corrupted regime $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely.
--
--   The sums $I_1,\dots,I_4$ are those of the definition `IAFTRL_GTerms`.
--
--   **Claim.** There are constants $M,J$, independent of $T$, $C$ and the run, with
--   $$I_1=\beta_1h^*+\sum_{t=2}^T(\beta_t-\beta_{t-1})\,\mathbb E[h^*-D_{\mathrm{KL}}(q_t,\mu)]\le M+J\sqrt C\log(e+C).$$
--   This is Lemma G.1, $I_1\le\beta_1h^*+4A_LT_*^{-11/2}+h^*E_T$, combined with the weighted failure estimate $E_T\le16W_\theta[1+\sqrt C\log(e+C)]$ of (G.11)–(G.13) and Lemma G.26.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.2, Lemma G.1, and (G.11)–(G.13)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.1 (Relative-entropy penalty contribution).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.1, p.126:
"`I₁ := β₁h* + Σ_{t=2}^T (β_t − β_{t−1}) E[h* − D_KL(q_t, µ)] ≤ β₁h* + 4A_L T*^{−11/2} + h* E_T`",
combined with the weighted failure estimate (G.11)–(G.13) (Lemma G.26):
`(h* + 10d) E_T ≤ E_θ [1 + √C log(e + C)]`.

In the sharp corrupted setting there are instance constants `M, J` (independent of `T`, `C` and the
run) with `I₁ ≤ M + J √C log(e + C)`. -/
theorem lemma_G_1 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        penI1 P ℬ e T R astar ≤ M + J * Real.sqrt C * Real.log (Real.exp 1 + C) := by sorry

end IAFTRL
