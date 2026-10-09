-- Prove2me | Theorems.Thm_LinearMDPRL_Misspec_lsvi_ucb_misspecified_regret
-- name    : LinearMDPRL.Misspec.lsvi_ucb_misspecified_regret
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:36:54.358202+00:00
-- url     : https://prove2.me/theorems/8986d692-dcaa-46e8-b15f-ec08646a83c7
-- title:
--   Theorem 3.2, p. 8 — LSVI-UCB with λ = 1, β_k = c(d√ι + ζ√(kd))H: w.p. 1 − p, Regret(K) ≤ C(√(d³H³Tι²) + ζdHT√ι)
-- statement:
--   There exist absolute constants $c>0$ and $C>0$ with the following property. Let $\mathrm{MDP}(\mathcal S,\mathcal A,H,\mathbb P,r)$ be a $\zeta$-approximately linear MDP with feature map $\phi:\mathcal S\times\mathcal A\to\mathbb R^d$ (Assumption B), with $d,H,K\ge1$, and let $p\in(0,1)$, $T=KH$ and $\iota=\log(2dT/p)$. Run LSVI-UCB (Algorithm 1) for $K$ episodes with
--   $$\lambda=1,\qquad\beta_k=c\cdot(d\sqrt\iota+\zeta\sqrt{kd})H,$$
--   against initial states chosen by an adaptive adversary. Then, with probability at least $1-p$,
--   $$\mathrm{Regret}(K)=\sum_{k=1}^K\big[V^\star_1(x^k_1)-V^{\pi_k}_1(x^k_1)\big]\le C\cdot\Big(\sqrt{d^3H^3T\iota^2}+\zeta dHT\sqrt\iota\Big).$$
--
--   The algorithm is robust to model misspecification: compared with Theorem 3.1 it pays an additional regret of order $\zeta dHT\sqrt\iota$, linear in $T$ because of the intrinsic bias of linear approximation.
--
--   **Formalization Note** The constants $c$ and $C$ are quantified before every type, dimension, horizon, misspecification level, probability level and run, so they are absolute; "$O(\cdot)$" is the constant $C$. "With probability $1-p$" is written as: the (outer) measure of the set where the regret exceeds the bound is at most $p$. $V^{\pi_k}_1$ is the model value of the greedy policy of episode $k$. The hypotheses $d,H,K\ge1$ are implicit on the page ($\iota$ needs $dT>0$). The interaction is given by an arbitrary filtration to which the states are adapted, with the transition law holding conditionally on the past. Assumption B uses the total-variation normalization of $\mu_h$ described in its definition. At $\zeta=0$ the statement is Theorem 3.1 under the same normalization.
-- source:
--   arXiv:1907.05388v2, Theorem 3.2, p. 8 (restated p. 25)

import Mathlib
import Definitions.Def_LinearMDPRL_Linear_Model
import Definitions.Def_LinearMDPRL_Linear_LSVIUCB
import Definitions.Def_LinearMDPRL_Misspec_ApproxLinearMDP
import Definitions.Def_LinearMDPRL_Misspec_Event

open MeasureTheory ProbabilityTheory Matrix

namespace LinearMDPRL.Misspec

universe u v w

/-- **Theorem 3.2** (p. 8). Under Assumption B there are absolute constants `c, C > 0` such that,
for every `p ∈ (0, 1)`, LSVI-UCB (Algorithm 1) with `λ = 1` and `β_k = c (d√ι + ζ√(kd)) H`,
`ι = log(2dT/p)`, `T = KH`, has, with probability at least `1 − p`,
`Regret(K) ≤ C (√(d³H³Tι²) + ζ d H T √ι)`. -/
theorem lsvi_ucb_misspecified_regret :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ {S : Type u} {A : Type v} [MeasurableSpace S] [Fintype A] [Nonempty A] [LinearOrder A]
      [MeasurableSpace A] [DiscreteMeasurableSpace A] (d H K : ℕ), 1 ≤ d → 1 ≤ H → 1 ≤ K →
    ∀ (M : LinearMDPRL.Linear.EpisodicMDP S A) (φ : S → A → EuclideanSpace ℝ (Fin d)) (ζ : ℝ),
      IsApproxLinearMDP M H d φ ζ →
    ∀ p : ℝ, 0 < p → p < 1 →
    ∀ {Ω : Type w} [mΩ : MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (𝓕 : Filtration ℕ mΩ) (x : ℕ → ℕ → Ω → S) (a : ℕ → ℕ → Ω → A),
      LinearMDPRL.Linear.IsLSVIUCBRun μ 𝓕 M φ 1 (betaMis c ζ d H K p) H K x a →
      μ {ω | C * (Real.sqrt ((d : ℝ) ^ 3 * (H : ℝ) ^ 3 * ((K : ℝ) * H) * LinearMDPRL.Linear.iota d K H p ^ 2)
                + ζ * d * H * ((K : ℝ) * H) * Real.sqrt (LinearMDPRL.Linear.iota d K H p))
              < LinearMDPRL.Linear.regret M φ 1 (betaMis c ζ d H K p) H K
                  (fun τ i => x τ i ω) (fun τ i => a τ i ω)}
        ≤ ENNReal.ofReal p := by sorry

end LinearMDPRL.Misspec
