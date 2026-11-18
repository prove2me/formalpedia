-- Prove2me | Theorems.Thm_IAFTRL_theorem_3_2_ii
-- name    : IAFTRL.theorem_3_2_ii
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T04:21:05.260128+00:00
-- url     : https://prove2.me/theorems/373ff1c5-3e62-4d79-864b-d718c4dfd950
-- title:
--   Theorem 3.2(ii) — corruption lower bound $\frac1{32}\min\{\sqrt T,\sqrt{C/\varphi}\}$ on a sharp arch with small modulus
-- statement:
--   **Setting.** Let
--   $$
--   \mathcal A_{\rm arch}=\Big\{a(x)=\Big(x,\ \frac{1-x^2}{2}\Big):-1\le x\le1\Big\},\qquad \theta_\sigma=\Big(\frac{\sigma\varphi}{2},\frac12\Big),\quad\sigma\in\{-1,1\},\quad 0<\varphi\le\frac18 .
--   $$
--   The unique optimal action of $\theta_\sigma$ is $a^*=-\sigma e_1=(-\sigma,0)$. Let $\varsigma_\sigma$ be the sharpness modulus (1.3) with generator $\mathcal A_{\rm arch}$, and $c^*_{\rm ctr}$ the centered information-acquisition complexity (1.4).
--
--   **Claim.** For each $\sigma=\pm1$, $a^*=-\sigma e_1\in\mathcal A_{\rm arch}$ is the unique optimal action, and
--   $$
--   \frac\varphi6\le\varsigma_\sigma\le\frac\varphi2,\qquad \frac{128}{25}\le c^*_{\rm ctr}(\mathcal A_{\rm arch},\theta_\sigma)\le10 .
--   $$
--   Moreover, take any corruption budget $C\ge\varphi^{-1}$ and any integer $T\ge\lceil\varphi^{-2}\rceil$. There exist two corrupted stochastic environments $E_{+1},E_{-1}$ over the horizon $T$, where $E_\sigma$ has fixed loss vector $\theta_\sigma$, a deterministic corruption sequence of total budget at most $C$, and feedback in $[-1,1]$ with the linear mean. For these environments, every policy that plays only actions of $\mathcal A_{\rm arch}$ satisfies
--   $$
--   \max_{\sigma=\pm1}\mathrm{Reg}_{T,\sigma}\ \ge\ \frac1{32}\min\Big\{\sqrt T,\ \sqrt{C/\varphi}\Big\}.
--   $$
--
--   The instances stay sharp and $c^*_{\rm ctr}$ stays bounded, but the corruption penalty grows like $\sqrt{C/\varsigma_\sigma}$ as the modulus $\varsigma_\sigma\asymp\varphi\to0$. So the dependence of the $\sqrt C$ term on the geometry in Theorem 3.1 is necessary.
--
--   **Formalization Note** The environments are oblivious (`LinEnv`), and the regret is $\sup_{u\in\mathcal A}\mathbb E[\sum_{t\le T}(A_t-u)^\top\theta_t]$ against the actual loss vectors (`LinEnv.regret`). The sharpness modulus is `sharpModulus arch (θ σ) ![-σ, 0]`.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Section 3.3, Theorem 3.2 (second bullet), pp.25–26; proof in Appendix H.2 and Lemma H.1 (H.5)–(H.7), pp.194–198

import Mathlib
import Definitions.Def_LinearBanditProtocol
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_SignModel

namespace IAFTRL

open MeasureTheory ProbabilityTheory Matrix BanditAlgorithm

/-- **Theorem 3.2, second part (corruption on a sharp instance with arbitrarily small gaps).**
Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Theorem 3.2,
pp.25–26: "Let `A_arch = {(x, (1 − x²)/2) : −1 ≤ x ≤ 1}`, `θ_σ = (σϕ/2, 1/2)`, and `σ = ±1`, where
`0 < ϕ ≤ 1/8`. For each `σ = ±1`, the sharpness modulus `ς_σ` in (1.3) and the centered
information-acquisition complexity satisfy `ϕ/6 ≤ ς_σ ≤ ϕ/2` and
`128/25 ≤ c*_ctr(A_arch, θ_σ) ≤ 10`. For every corruption budget `C ≥ ϕ⁻¹` and every integer
`T ≥ ⌈ϕ⁻²⌉`, there exist two corrupted stochastic environments indexed by `σ = ±1`, each with fixed
loss vector `θ_σ` and a deterministic corruption sequence of total budget at most `C`, such that
every policy satisfies `max_{σ=±1} Reg_{T,σ} ≥ (1/32) min{√T, √(C/ϕ)}`."

The unique optimal action of `θ_σ` is `a* = −σe₁ = (−σ, 0)` (Lemma H.1, p.196); the sharpness
modulus and `c*_ctr` are taken at this `a*`, with generator `ℬ = A_arch`. The environments are
oblivious (`LinEnv`), and a policy is any `LinearBanditPolicy 2` that plays only actions of
`A_arch`. -/
theorem theorem_3_2_ii (φ : ℝ) (hφ : 0 < φ) (hφ' : φ ≤ 1 / 8) :
    let arch : Set (Fin 2 → ℝ) := {a | ∃ x ∈ Set.Icc (-1 : ℝ) 1, a = ![x, (1 - x ^ 2) / 2]}
    let θ : ℝ → Fin 2 → ℝ := fun σ => ![σ * φ / 2, 1 / 2]
    (∀ σ : ℝ, (σ = 1 ∨ σ = -1) →
      ![-σ, 0] ∈ arch ∧ (∀ a ∈ arch, a ≠ ![-σ, 0] → ![-σ, 0] ⬝ᵥ θ σ < a ⬝ᵥ θ σ) ∧
      φ / 6 ≤ sharpModulus arch (θ σ) ![-σ, 0] ∧ sharpModulus arch (θ σ) ![-σ, 0] ≤ φ / 2 ∧
      128 / 25 ≤ cstarCtr arch (θ σ) ![-σ, 0] ∧ cstarCtr arch (θ σ) ![-σ, 0] ≤ 10) ∧
    ∀ C : ℝ, φ⁻¹ ≤ C → ∀ T : ℕ, ⌈(φ ^ 2)⁻¹⌉₊ ≤ T →
      ∃ E : ℝ → LinEnv 2,
        (∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (E σ).IsCorruptedStoch arch (θ σ) C T) ∧
        ∀ π : LinearBanditPolicy 2, IsSupportedLinearPolicy arch π →
          (1 / 32) * min (Real.sqrt T) (Real.sqrt (C / φ)) ≤
            max ((E 1).regret arch π T) ((E (-1)).regret arch π T) := by sorry

end IAFTRL
