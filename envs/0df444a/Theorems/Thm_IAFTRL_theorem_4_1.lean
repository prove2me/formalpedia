-- Prove2me | Theorems.Thm_IAFTRL_theorem_4_1
-- name    : IAFTRL.theorem_4_1
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:20:53.268203+00:00
-- url     : https://prove2.me/theorems/179f75da-0f2f-463c-8926-a28e85fea3e1
-- title:
--   Theorem 4.1 — impossibility of an $O(\sqrt C)$ corruption guarantee beyond sharpness
-- statement:
--   **Setting.** For an even integer $p\ge4$ let
--   $$
--   \mathcal A_p=\Big\{a(s)=\Big(\frac12+s,\ s^p\Big):|s|\le\frac14\Big\},\qquad \theta_0=(0,1),\qquad a_0=\Big(\frac12,0\Big).
--   $$
--
--   **Claim.** $a_0\in\mathcal A_p$ is the unique optimal action under $\theta_0$. The instance $(\mathcal A_p,\theta_0)$ is not geometrically sharp, and $c^*_{\rm ctr}(\mathcal A_p,\theta_0)=\infty$: no finite centered feasible sampling allocation (1.4) exists. Moreover, take any $C\ge0$ and any integer $T\ge\max\{1,[4^{p-1}/(8p)]^2\}$. There exist two corrupted stochastic environments $E_{+1},E_{-1}$ over the horizon $T$ that share the same fixed loss vector $\theta_0$. Only the deterministic corruption sequence depends on $\sigma$, and each has total corruption budget at most $C$ and feedback in $[-1,1]$ with the linear mean. For these environments, every policy that plays only actions of $\mathcal A_p$ satisfies
--   $$
--   \max_{\sigma=\pm1}\mathrm{Reg}_{T,\sigma}\ \ge\ \frac{(p-1)T}{4p^{p/(p-1)}}\,\min\Big\{\frac{4C}{3T},\ \frac1{8\sqrt T}\Big\}^{p/(p-1)} .\qquad(4.1)
--   $$
--
--   At $C=3\sqrt T/32$ this gives a regret lower bound of order $C^{(p-2)/(p-1)}$. Hence no bound of the form $A\log T+M+J\,C^\gamma[\log T]^q$ with instance-dependent constants and $\gamma<1$ holds on all nonsharp instances, and the $O(\sqrt C)$ guarantee of Theorem 3.1 cannot be extended beyond sharpness.
--
--   **Formalization Note** Non-sharpness is `¬ IsSharp Ap θ₀ a₀` (Definition 1.1 with generator $\mathcal A_p$), and $c^*_{\rm ctr}=\infty$ is `∀ n, ¬ IsCtrAlloc Ap θ₀ a₀ n`. The environments are oblivious (`LinEnv`), and the regret is measured against the actual loss vectors (`LinEnv.regret`). The horizon condition is the real inequality $(4^{p-1}/(8p))^2\le T$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 4, Theorem 4.1 (4.1), p.26; proof in Appendix I (I.1) and Lemma I.1, pp.200–203

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

/-- **Theorem 4.1 (impossibility of an `O(√C)` corruption guarantee beyond sharpness).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Theorem 4.1, p.26:
"For every even integer `p ≥ 4`, let `A_p = {(1/2 + s, s^p) : |s| ≤ 1/4}` and `θ₀ = (0, 1)`.
This fixed compact set has a unique optimal action `a₀ = (1/2, 0)`, but is not sharp and has
`c*_ctr = ∞`. For every `C ≥ 0` and every integer `T ≥ max{1, [4^{p−1}/(8p)]²}`, there exist two
corrupted stochastic environments indexed by `σ ∈ {−1, +1}` that share the same fixed loss vector
`θ₀`. Only the deterministic corruption sequence depends on `σ`, and in both environments the
total corruption budget is at most `C`. For every policy, these environments satisfy
`max_{σ=±1} Reg_{T,σ} ≥ ((p − 1)T / (4 p^{p/(p−1)})) · min{4C/(3T), 1/(8√T)}^{p/(p−1)}`." (4.1)

Non-sharpness is `¬ IsSharp A_p θ₀ a₀` (Definition 1.1 with generator `ℬ = A_p`), and
`c*_ctr = ∞` means that no finite centered feasible sampling allocation (1.4) exists
(Lemma I.1, p.202). The environments are oblivious (`LinEnv`), and a policy is any
`LinearBanditPolicy 2` that plays only actions of `A_p`. -/
theorem theorem_4_1 (p : ℕ) (hp : 4 ≤ p) (hpe : Even p) :
    let Ap : Set (Fin 2 → ℝ) := {a | ∃ s ∈ Set.Icc (-(1 / 4) : ℝ) (1 / 4), a = ![1 / 2 + s, s ^ p]}
    let θ₀ : Fin 2 → ℝ := ![0, 1]
    let a₀ : Fin 2 → ℝ := ![1 / 2, 0]
    (a₀ ∈ Ap ∧ (∀ a ∈ Ap, a ≠ a₀ → a₀ ⬝ᵥ θ₀ < a ⬝ᵥ θ₀) ∧ ¬ IsSharp Ap θ₀ a₀ ∧
      ∀ n : Measure (Fin 2 → ℝ), ¬ IsCtrAlloc Ap θ₀ a₀ n) ∧
    ∀ C : ℝ, 0 ≤ C → ∀ T : ℕ, 1 ≤ T → ((4 : ℝ) ^ (p - 1) / (8 * p)) ^ 2 ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch Ap θ₀ C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy Ap π →
          ((p : ℝ) - 1) * T / (4 * (p : ℝ) ^ ((p : ℝ) / (p - 1))) *
              (min (4 * C / (3 * T)) (1 / (8 * Real.sqrt T))) ^ ((p : ℝ) / (p - 1)) ≤
            max ((E 1).regret Ap π T) ((E (-1)).regret Ap π T) := by sorry

end IAFTRL
