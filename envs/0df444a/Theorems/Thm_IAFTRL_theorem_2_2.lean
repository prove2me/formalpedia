-- Prove2me | Theorems.Thm_IAFTRL_theorem_2_2
-- name    : IAFTRL.theorem_2_2
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T06:23:16.962666+00:00
-- url     : https://prove2.me/theorems/e7d4e777-1dd7-467e-b50e-af0872dd04f6
-- title:
--   Theorem 2.2 — finite-action corruption lower bound $\Omega(\min\{\sqrt T,\sqrt{C/\Delta_{\min}}\})$ with $c^*=\Theta(1)$
-- statement:
--   Let $e_1,e_2$ be the standard basis of $\mathbb R^2$ and $\mathcal A=\{-e_1,e_1,e_2\}$. For $0<\Delta_{\min}\le1/2$ and $\sigma=\pm1$, let $\theta_\sigma=(\sigma\Delta_{\min}/2,\,1/2)$. Losses are minimized, so the unique optimal action of $\theta_\sigma$ is $-\sigma e_1$.
--
--   1. **The instances.** For each $\sigma=\pm1$, the instance $(\mathcal A,\theta_\sigma)$ has a unique optimal action and minimum gap exactly $\Delta_{\min}$. Its information-acquisition complexity (1.2) is
--   $$
--   c^*(\mathcal A,\theta_\sigma)=\frac{4}{1+\Delta_{\min}}=\Theta(1).
--   $$
--   2. **The lower bound.** Fix a corruption budget $C\ge\Delta_{\min}^{-1}$ and an integer $T\ge\lceil\Delta_{\min}^{-2}\rceil$. Then there are two corrupted stochastic environments, indexed by $\sigma=\pm1$, with the following properties. Each has fixed loss vector $\theta_\sigma$, bounded feedback in $[-1,1]$ with mean $a^\top\theta_t$, and total corruption $\sum_{t\le T}\|\theta_t-\theta_\sigma\|_{\mathcal A}\le C$. Moreover, every policy $\pi$ that plays actions in $\mathcal A$ satisfies
--   $$
--   \max_{\sigma=\pm1}\mathrm{Reg}_{T,\sigma}(\pi)\ \ge\ \frac1{16}\min\Big\{\sqrt T,\ \sqrt{C/\Delta_{\min}}\Big\}.
--   $$
--   Here $\mathrm{Reg}_{T,\sigma}=\sup_{u\in\mathcal A}\mathbb E\big[\sum_{t\le T}(A_t-u)^\top\theta_t\big]$ is computed in the environment indexed by $\sigma$, using the actual (corrupted) loss vectors $\theta_t$.
--
--   The two instances keep $c^*$ bounded while $\Delta_{\min}$ can be arbitrarily small. The theorem therefore shows that the coefficient of $\sqrt C$ in the corruption term of a regret bound cannot, in general, be bounded in terms of $c^*$ alone; it must grow like $\Delta_{\min}^{-1/2}$. This complements the $J_{d,K,\Delta_{\min}}\sqrt C$ term of Theorem 2.1.
--
--   **Formalization Note.** The actions are listed as `arms = (−e₁, e₁, e₂)`, and $\mathcal A$ is `Set.range arms`. The complexity $c^*$ is `linearBanditAllocationValue arms (−θ)`, the loss-convention reading of (1.2) also used in Theorem 2.1. A policy is any `LinearBanditPolicy 2` (Markov kernels from histories to actions) with `IsSupportedLinearPolicy (Set.range arms) π`. The environments are oblivious `LinEnv`s (definition `IAFTRL_LinEnv`), with deterministic corruption and feedback laws that depend only on the round and the action. Exhibiting environments in this subclass is at least as strong as the source's existence claim. The condition $T\ge\lceil\Delta_{\min}^{-2}\rceil$ is written `⌈(Δ ^ 2)⁻¹⌉₊ ≤ T`.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 2.3, Theorem 2.2, p. 20; setting of Section 1.1 (pp. 5–6), c* defined in (1.2); proof in Appendix E (pp. 112–115)

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_IsUniqueMin
import Definitions.Def_IAFTRL_LinEnv

namespace IAFTRL

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

/-- **Theorem 2.2 (finite-action corruption lower bound).** Zhao–Tan, *Best-of-Both-Worlds FTRL
for Linear Bandits* (STOC submission version), Theorem 2.2, p.20: "Let `𝒜 = {−e₁, e₁, e₂}` and
`θ_σ = (σΔ_min/2, 1/2)`, with `σ = ±1` and `0 < Δ_min ≤ 1/2`. Both instances have minimum gap
`Δ_min` and `c*(𝒜, θ_σ) = 4/(1+Δ_min) = Θ(1)` for all `0 < Δ_min ≤ 1/2`. For every corruption
budget `C ≥ Δ_min⁻¹` and every integer `T ≥ ⌈Δ_min⁻²⌉`, there are two corrupted stochastic
environments indexed by `σ = ±1`, each with loss vector `θ_σ`, such that every policy satisfies
`max_{σ=±1} Reg_{T,σ} ≥ (1/16) min{√T, √(C/Δ_min)}` in the corrupted stochastic regime with budget
at most `C`."

The actions are listed as `arms = (−e₁, e₁, e₂)`; `c*` is `linearBanditAllocationValue arms (−θ)`
(the loss convention of (1.2), as in Theorem 2.1). A policy is any `LinearBanditPolicy 2` that
plays only actions of `𝒜`. The two environments are oblivious (`LinEnv`): deterministic
corruption and feedback whose law depends only on the round and the action. -/
theorem theorem_2_2 (Δ : ℝ) (hΔ : 0 < Δ) (hΔ' : Δ ≤ 1 / 2) :
    let arms : Fin 3 → Fin 2 → ℝ := ![![-1, 0], ![1, 0], ![0, 1]]
    let θ : ℝ → Fin 2 → ℝ := fun σ => ![σ * Δ / 2, 1 / 2]
    (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      (∃ jstar : Fin 3, IsUniqueMin arms (θ σ) jstar ∧
        (∀ j, j ≠ jstar → Δ ≤ (arms j - arms jstar) ⬝ᵥ θ σ) ∧
        ∃ j, j ≠ jstar ∧ (arms j - arms jstar) ⬝ᵥ θ σ = Δ) ∧
      linearBanditAllocationValue arms (-θ σ) = 4 / (1 + Δ)) ∧
    ∀ C : ℝ, Δ⁻¹ ≤ C → ∀ T : ℕ, ⌈(Δ ^ 2)⁻¹⌉₊ ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch (Set.range arms) (θ σ) C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy (Set.range arms) π →
          (1 / 16) * min (Real.sqrt T) (Real.sqrt (C / Δ)) ≤
            max ((E 1).regret (Set.range arms) π T) ((E (-1)).regret (Set.range arms) π T) := by sorry

end IAFTRL
