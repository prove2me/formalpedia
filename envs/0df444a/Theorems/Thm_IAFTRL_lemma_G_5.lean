-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_5
-- name    : IAFTRL.lemma_G_5
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:47:03.963234+00:00
-- url     : https://prove2.me/theorems/f61087b8-5428-4970-9372-12105d9f843d
-- title:
--   Lemma G.5 — exploration contribution of GIA-FTRL under the fixed loss vector
-- statement:
--   **Setting.** The setting is that of Proposition G.1 (`proposition_G_1_anc`):
--   - a GIA-FTRL run on a compact generator $\mathcal B$ of a compact spanning $\mathcal A\subseteq\mathbb B^d$, with $k\ge1$;
--   - a sharp instance $(\theta,a^*)$ with $\|\theta\|_{\mathcal A}\le1$ and unique optimal action $a^*\in\mathcal A$;
--   - the corrupted regime $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely.
--
--   The sums $I_1,\dots,I_4$ are those of the definition `IAFTRL_GTerms`.
--
--   **Claim.** There is $J$ such that for every finite feasible centered sampling allocation $n$ on $\mathcal B$ there is $M$, independent of $T$, $C$ and the run, with
--   $$I_3=\sum_{t=1}^T\mathbb E\langle p_t-q_t,\Delta\rangle\le16\,B\,C_{\mathrm{rat}}^4\,c^n_{\mathrm{ctr}}\log(eT)+M+J\sqrt C\log(e+C),$$
--   where $B=2^{36}(d+1)$ and $C_{\mathrm{rat}}=64$. This is Lemma G.5 combined with the weighted failure estimate.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.4, Lemma G.5, and (G.11)–(G.13)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_GTerms

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.5 (Exploration contribution under the fixed loss vector).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.5,
p.131: "For a fixed feasible centered sampling allocation `n_des` …
`I₃ := Σ_t E[⟨p_t − q_t, Δ⟩] ≤ 16 B C_rat⁴ c^{n_des}_ctr log(eT) + M_{3,θ,n_des} + 8d E_T`",
combined with the weighted failure estimate (G.11)–(G.13) (Lemma G.26); `B = 2^36(d+1)`,
`C_rat = 64`.

In the sharp corrupted setting there is `J` such that for every finite feasible centered
allocation `n` on `ℬ` there is `M` (independent of `T`, `C` and the run) with
`I₃ ≤ 16 B C_rat⁴ c^n_ctr log(eT) + M + J √C log(e + C)`. -/
theorem lemma_G_5 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        exploI3 P ℬ e T R θ astar ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by sorry

end IAFTRL
