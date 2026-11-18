-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_4
-- name    : IAFTRL.lemma_G_4
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:46:55.414278+00:00
-- url     : https://prove2.me/theorems/45bd9383-7bc7-4cf2-8f44-df2aa197cece
-- title:
--   Lemma G.4 — relative-entropy stability contribution of GIA-FTRL
-- statement:
--   **Setting.** The setting is that of Proposition G.1 (`proposition_G_1_anc`):
--   - a GIA-FTRL run on a compact generator $\mathcal B$ of a compact spanning $\mathcal A\subseteq\mathbb B^d$, with $k\ge1$;
--   - a sharp instance $(\theta,a^*)$ with $\|\theta\|_{\mathcal A}\le1$ and unique optimal action $a^*\in\mathcal A$;
--   - the corrupted regime $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely.
--
--   The sums $I_1,\dots,I_4$ are those of the definition `IAFTRL_GTerms`.
--
--   **Claim.** There are constants $M,J$, independent of $T$, $C$ and the run, with
--   $$I_2=\sum_{t=1}^T\mathbb E[D_t]\le M+J\sqrt C\log(e+C),\qquad D_t=\langle q_t,\hat f_t\rangle+\beta_t\log\langle q_t,e^{-\hat f_t/\beta_t}\rangle .$$
--   This is Lemma G.4, $I_2\le34e^2A_LT_*^{-9/2}+2dE_T$, combined with the weighted failure estimate.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.3, Lemma G.4, and (G.11)–(G.13)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.4 (Relative-entropy stability contribution).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.4, p.130:
"For `D_t = ⟨q_t, f̂_t⟩ + β_t log⟨q_t, e^{−f̂_t/β_t}⟩`, `I₂ := Σ_t E[D_t] ≤ 34e² A_L T*^{−9/2} + 2d E_T`",
combined with the weighted failure estimate (G.11)–(G.13) (Lemma G.26).

In the sharp corrupted setting there are instance constants `M, J` (independent of `T`, `C` and the
run) with `I₂ ≤ M + J √C log(e + C)`. -/
theorem lemma_G_4 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ M J : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        stabI2 P ℬ e T R ≤ M + J * Real.sqrt C * Real.log (Real.exp 1 + C) := by sorry

end IAFTRL
