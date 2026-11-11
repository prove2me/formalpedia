-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_4_2
-- name    : JuHardCoreTransition.Mixing.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:23.641917+00:00
-- url     : https://prove2.me/theorems/c0640abf-8512-4d6b-b178-eb7359f968f8
-- title:
--   Lemma 4.2 — mixing and relaxation from field-dynamics spectral stability
-- statement:
--   Let $G$ have $n\ge1$ vertices and let $\lambda>0$. Suppose $\mu_{G,\lambda}$ satisfies field-dynamics spectral stability with a nondecreasing rate $\mathcal C:(0,\lambda]\to[1,\infty)$, set $I=\int_0^\lambda\frac{\mathcal C(a)-1}a\,da$ and assume $I<\infty$. Let $\bar\lambda\ge\max\{1,\lambda\}$, and suppose $\mu_{G,\lambda}$ satisfies the occupied-marginal lower-bound condition under positive pinning with parameter $b>0$: $\mu_{G,\lambda}(X_v=1\mid X_w=1\ \forall w\in S)\ge b$ for every independent $S$ and every $v\notin N_G[S]$. Then the Glauber dynamics for $\mu_{G,\lambda}$ has
--   $$t_{\mathrm{mix}}(\eta)\le C\bar\lambda ne^I\Big[\log\frac{n\bar\lambda}b\,\log\log\frac{e^2}{\mu_{\min}}+\log\frac1\eta\Big]\qquad(0<\eta<1/4),$$
--   where $\mu_{\min}=\min_{J\in\mathcal I(G)}\mu_{G,\lambda}(J)$ and $C$ is an absolute constant. Without the occupied-marginal lower bound, $t_{\mathrm{rel}}\le n(1+\bar\lambda)e^I$.
--
--   Differences from the source:
--   - encoding: an n-vertex graph G=(V,E) → a SimpleGraph on Fin n (n labelled vertices); reason: every finite graph is isomorphic to one on Fin n and every quantity involved is isomorphism-invariant; this lets the absolute constant be stated before the graph
--   - encoding: a nondecreasing rate C : (0, λ] → [1, ∞) → Crate : ℝ → ℝ, MonotoneOn on (0, λ] and ≥ 1 there (values elsewhere unused); reason: only the values on (0, λ] enter
--   - encoding: I < ∞ → stabIntegral Crate λ ≠ ⊤, with e^I = exp of its real value; reason: for a nonnegative integrand the improper integral is the Lebesgue integral
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 4.2, printed p.18 / PDF p.19

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

/-- **Lemma 4.2 (Mixing and relaxation from field-dynamics spectral stability)** (printed p.18 /
PDF p.19). Let `G` have `n ≥ 1` vertices and `λ > 0`. Suppose `μ_{G,λ}` satisfies field-dynamics
spectral stability with a nondecreasing rate `C : (0, λ] → [1, ∞)`, and
`I = ∫_0^λ (C(a) − 1)/a da < ∞`. Let `λ̄ ≥ max{1, λ}`. If `μ_{G,λ}` satisfies the occupied-marginal
lower bound under positive pinning with parameter `b > 0`, then for `0 < η < 1/4`
`t_mix(η) ≤ K λ̄ n e^I [log(nλ̄/b) · log log(e²/μ_min) + log(1/η)]` (4.2), with `K` absolute and
`μ_min = min_{J ∈ I(G)} μ_{G,λ}(J)`. Without the occupied-marginal bound,
`t_rel ≤ n(1 + λ̄)e^I` (4.3). (The vertex set of an `n`-vertex graph is `Fin n`.) -/
theorem lemma_4_2 :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      ∀ lam : ℝ, 0 < lam → ∀ Crate : ℝ → ℝ, MonotoneOn Crate (Set.Ioc 0 lam) →
        (∀ a ∈ Set.Ioc (0 : ℝ) lam, 1 ≤ Crate a) → IsStabilityRate G lam Crate →
        stabIntegral Crate lam ≠ ⊤ → ∀ lamBar : ℝ, max 1 lam ≤ lamBar →
          (∀ b : ℝ, 0 < b → OccupiedMarginalLB G lam b → ∀ η : ℝ, 0 < η → η < 1 / 4 →
            (tmixG G lam η : ℝ) ≤
              K * lamBar * n * Real.exp (stabIntegral Crate lam).toReal *
                (Real.log ((n : ℝ) * lamBar / b) *
                    Real.log (Real.log (Real.exp 2 / muMinG G lam)) + Real.log (1 / η))) ∧
          trelG G lam ≤ n * (1 + lamBar) * Real.exp (stabIntegral Crate lam).toReal := by sorry

end JuHardCoreTransition.Mixing
