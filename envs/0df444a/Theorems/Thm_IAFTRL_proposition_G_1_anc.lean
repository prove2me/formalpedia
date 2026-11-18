-- Prove2me | Theorems.Thm_IAFTRL_proposition_G_1_anc
-- name    : IAFTRL.proposition_G_1_anc
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T13:16:17.87718+00:00
-- url     : https://prove2.me/theorems/b0256a2c-38c7-45b5-80d3-fa2eaacb8319
-- title:
--   Proposition G.1 (G.1) — corrupted bound of GIA-FTRL against the optimal action
-- statement:
--   **Setting.** The setting is that of Proposition G.1:
--   - a GIA-FTRL run on a compact generator $\mathcal B$ of a compact spanning $\mathcal A\subseteq\mathbb B^d$;
--   - a sharp instance $(\theta,a^*)$ with $\|\theta\|_{\mathcal A}\le1$ and unique optimal action $a^*\in\mathcal A$;
--   - the corrupted stochastic regime with budget $C\ge0$, i.e. $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely.
--
--   **Claim (G.1).** There is $J^{\mathrm{anc}}_\theta$ such that for every finite feasible centered sampling allocation $n$ on $\mathcal B$ there is $M_n$, independent of $T$, $C$ and the run, with
--   $$\mathrm{Reg}_T(a^*)=\mathbb E\Big[\sum_{t<T}(A_t-a^*)^\top\theta_t\Big]\le16\,B\,C_{\mathrm{rat}}^4\,c^n_{\mathrm{ctr}}(\mathcal B,\theta)\log(eT)+M_n+J^{\mathrm{anc}}_\theta\sqrt C\log(e+C),$$
--   where $B=2^{36}(d+1)$ and $C_{\mathrm{rat}}=64$.
--
--   **Proof outline.**
--   - The master decomposition (G.3)–(G.5) combines the localized entropy identity (J.5), the proxy function, and the exploration and direct-corruption integrals.
--   - The four terms are bounded by Lemmas G.1 (penalty), G.4 (stability), G.5 (exploration) and G.9 (corruption).
--   - The weighted failure estimate is Lemma G.26.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.1.1, Proposition G.1, (G.1) and its proof (G.3)–(G.22), pp. 123–125

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Proposition G.1, comparator `a*` (G.1).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear
Bandits* (STOC submission version), Proposition G.1, p.123: "GIA-FTRL, with a fixed finite
feasible centered sampling allocation `n_des`, satisfies for every `T ≥ 1` and every allowed budget
`C ≥ 0`: `Reg_T(a*) ≤ 16 B C_rat⁴ c^{n_des}_ctr log(eT) + M_{n_des} + J^anc_θ √C log(e + C)` (G.1)",
with `B = 2^36(d+1)` and `C_rat = 64`; `J^anc_θ` does not depend on the allocation.

The setting is that of `proposition_3_1` (sharp instance `(θ, a*)`, `‖θ‖_𝒜 ≤ 1`, unique
optimal action `a* ∈ 𝒜`); `n` is a finite feasible centered sampling allocation on the generator
`ℬ`, `J` is chosen before `n`, and `M` depends on `n` but not on `T, C` or the run; the regret is
against the optimal action `a*`. -/
theorem proposition_G_1_anc {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        gRegretVs P T R astar ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by sorry

end IAFTRL
