-- Prove2me | Theorems.Thm_IAFTRL_proposition_G_1
-- name    : IAFTRL.proposition_G_1
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T09:15:54.052322+00:00
-- url     : https://prove2.me/theorems/8541e594-a04f-4062-b47f-42c3858d07d5
-- title:
--   Proposition G.1 — corrupted sharp-instance bound of GIA-FTRL for each allocation
-- statement:
--   **Setting.** The setting is that of Proposition 3.1.
--   - $\mathcal A\subseteq\mathbb B^d$ is compact and spanning, $\mathcal B$ is a compact generator with $k\ge1$, and $e$ is a surjective enumeration of $\mathbb Q^d$.
--   - The instance $(\theta,a^*)$ satisfies $\|\theta\|_{\mathcal A}\le1$; $a^*\in\mathcal A$ is the unique minimizer of $a\mapsto a^\top\theta$ on $\mathcal A$; and the instance is sharp: $\varsigma\|a-a^*\|_{\mathcal S}\le(a-a^*)^\top\theta$ on $\mathrm{Conv}\,\mathcal A$ for some $\varsigma>0$.
--
--   **Claim.** There is $J$ such that for every finite feasible centered sampling allocation $n$ on $\mathcal B$ there is $M$, independent of $T$, $C$ and the run, with the following property. For every GIA-FTRL run of $T\ge1$ rounds in the corrupted stochastic regime with budget $C\ge0$ (that is, $\sum_{t<T}\|\theta_t-\theta\|_{\mathcal A}\le C$ almost surely), and every $u\in\mathcal A$,
--   $$\mathrm{Reg}_T(u)\le 16\,B\,C_{\mathrm{rat}}^4\,c^n_{\mathrm{ctr}}(\mathcal B,\theta)\log(eT)+M+J\sqrt C\,\log(e+C),$$
--   where $B=2^{36}(d+1)$ and $C_{\mathrm{rat}}=64$.
--
--   **Proof outline** (Appendix G.1.1). The regret against $a^*$ splits into a penalty term, a stability term, an exploration term and a direct corruption term (G.3)–(G.5). These are bounded by Lemmas G.1, G.4, G.5 and G.9 on the good events, together with the weighted failure estimate. The comparator correction for $u\ne a^*$ is then handled explicitly.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.1.1, Proposition G.1, pp. 123–124

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Proposition G.1 (Corrupted sharp-instance bound for each sampling allocation).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Proposition G.1,
pp.123–124: "GIA-FTRL, with a fixed finite feasible centered sampling allocation `n_des`,
satisfies for every `T ≥ 1` and every allowed budget `C ≥ 0` …
`Reg_T ≤ 16 B C_rat⁴ c^{n_des}_ctr log(eT) + M_{n_des} + J^cor_θ √C log(e + C)` (G.2)", with
`B = 2^36(d+1)` and `C_rat = 64` (G.264); `J^cor_θ` does not depend on the allocation.

The setting is that of `proposition_3_1` (sharp instance `(θ, a*)`, `‖θ‖_𝒜 ≤ 1`, unique
optimal action `a* ∈ 𝒜`); `n` is a finite feasible centered sampling allocation on the generator
`ℬ`, `J` is chosen before `n`, and `M` depends on `n` but not on `T, C` or the run. -/
theorem proposition_G_1 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ J : ℝ, ∀ n : Measure (Fin d → ℝ), IsCtrAlloc ℬ θ astar n →
      ∃ M : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        ∀ u ∈ 𝒜, gRegretVs P T R u ≤
          16 * gB d * 64 ^ 4 * ctrCost θ astar n * Real.log (Real.exp 1 * T) + M +
            J * Real.sqrt C * Real.log (Real.exp 1 + C) := by sorry

end IAFTRL
