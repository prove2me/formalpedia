-- Prove2me | Theorems.Thm_LearnManip_theorem_2
-- name    : LearnManip.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:04:59.935103+00:00
-- url     : https://prove2.me/theorems/07b0d283-bea8-4078-97df-5d2917fbfe7d
-- title:
--   Theorem 2, p.17, with $q^*$ of Theorem 1 (corrected: $\eta>0$ for attainment) — the closed-form optimal manipulation policy
-- statement:
--   Let $\alpha\in[0,1)$, $\gamma>0$, $\eta\ge0$, and let $G$, $s_{TH}$, $q^*$ be the closed forms of Theorem 1, with $\bar\eta=\min(\eta,1)$.
--
--   1. **Value.** For all $\mu$, $s,c\ge0$, the value function (8), the supremum over all admissible policies, is
--   $$V(\mu,s,c)=\frac{\mu}{1-\alpha}+G(s,c).$$
--   2. **BDP.** This function solves the BDP equation (10) at every state.
--   3. **Unique maximizer.** For $c>0$, the objective of (10) has exactly one maximizer. It is the quantity $q^*(s,c)$ together with the law with density
--   $$\Lambda^*(\mu,s,c)=\exp\Bigl(\frac{\mu_1^{q^*}-\mu}{\gamma(1-\alpha)}-\frac12\frac{\sigma^2_{\mu_1^{q^*}}}{\gamma^2(1-\alpha)^2}\Bigr)$$
--   with respect to the undistorted law of $\mu_1^{q^*}$, which is admissible, of finite relative entropy, and for which $\sigma^2_{\mu_1^{q^*}}=(s-s_{TH}(c))^+$.
--   4. **Mean boost.** That law is $N\bigl(\mu+\Delta^*(s,c),\ (s-s_{TH}(c))^+\bigr)$, with $\Delta^*(s,c)=\dfrac{\sigma^2_{\mu_1^{q^*}}}{(1-\alpha)\gamma}$.
--   5. **Attainment.** For $c_1>0$, $\eta>0$ and all $\mu_0$, $s_0\ge0$, there is a policy that uses $(q^*,\Lambda^*)$ at each period with the current variance and cost rate $c_1\eta^n$. It is admissible, it attains $V(\mu_0,s_0,c_1)$, and its partial sums converge to that value.
--
--   Among all distortions of the law of the posterior mean, the optimal one is thus a shift of the mean.
--
--   Differences from the source:
--   - reading: the (unique) optimal distortion rule → the value (8), the equation (10), the unique maximizer of (10), and the attainment by the Markov policy; reason: §4 opens by defining the policy as a solution of (10), and Lemma 1 makes such a solution optimal for (8), which is the paper's meaning of optimal
--   - reading: Λ* for all c → c > 0 in the maximizer clauses; reason: the proof assumes c > 0 (p.33); at c = 0 the paper has q* = ∞, which is not in ℝ₊, and no maximizer exists; the value and the BDP clauses keep c = 0
--   - correction: an optimal admissible policy for η ∈ [0, ∞) → attainment for η > 0; reason: at η = 0, s₀ > 0, every finite q has objective K(s − u) + αKu < Ks = G(s, 0) with u = s/(1 + sq) > 0, so no policy attains V; the other clauses keep η = 0
--   - reading: γ ∈ ℝ₊ → γ > 0; reason: the proofs assume it (p.33), and at γ = 0 the value is infinite
--   - reading: the expectation and the infinite sum of (8) → each µ_t integrable; the limsup of the partial sums in EReal, with costs in [0, ∞]; reason: the paper does not say when they are defined; this is the most generous reading for the firm
--   - encoding: a distortion rule Λ ∈ D_{µ^q} → the distorted law G ≪ N(µ, σ²_{µ^q}) with y G-integrable, and the cost γ KL(G‖N); reason: (4) is a bijection Λ ↔ P^Λ with Λ = dP^Λ/dP, and E[Λ log Λ] is the relative entropy
--   - encoding: supremum over all Λ in (10) → pairs (q, G) of finite relative entropy, with IsLUB; reason: a distortion of infinite relative entropy has objective −∞, so excluding it changes no supremum
--   - encoding: the filtration of the belief process (π_t) → histories of posterior means; reason: the variances are a function of the history
--   - encoding: periods t = 1, 2, … → periods n = 0, 1, … with t = n + 1; reason: the cost rate of period n + 1 is c₁ηⁿ
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Theorem 2, p.17, with Theorem 1, p.15, and the opening of §4, p.15

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_meanVar
import Definitions.Def_LearnManip_baseLaw
import Definitions.Def_LearnManip_IsDistortion
import Definitions.Def_LearnManip_Policy
import Definitions.Def_LearnManip_IsAdmissible
import Definitions.Def_LearnManip_horizonValue
import Definitions.Def_LearnManip_totalValue
import Definitions.Def_LearnManip_V
import Definitions.Def_LearnManip_bdpObjective
import Definitions.Def_LearnManip_IsBDPSolution
import Definitions.Def_LearnManip_sTH
import Definitions.Def_LearnManip_vClosed
import Definitions.Def_LearnManip_qStar
import Definitions.Def_LearnManip_boost
import Definitions.Def_LearnManip_Gstar
import Definitions.Def_LearnManip_IsOptimalPolicy

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Theorem 2, p.17, with `q*` of Theorem 1, p.15, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04):
the solution of the manipulation problem.

* (A) The value function (8), the supremum over all admissible policies, is `μ/(1−α) + G(s, c)`.
* (B) That function solves the BDP equation (10) at every state.
* (C) For `c > 0`, (10) has exactly one maximizer: `q*(s, c)` of (17), and the law with density `Λ*`
  of (19) with respect to the undistorted law of `μ^{q*}`, whose variance is `(s − s_TH(c))⁺`.
* (D) That law is `N(μ + ∆*(s, c), (s − s_TH(c))⁺)`, the mean boost (20).
* (E) For `c₁ > 0`, `η > 0`, the Markov policy `(q*, Λ*)` is admissible and attains `V`, with its partial
  sums converging.

**Formalization Note.** `c > 0` in (C) and `η > 0` in (E) are forced: at `c = 0` the paper's `q*` is `∞`
(p.33), and at `η = 0`, `s₀ > 0` no policy attains `V`. "(unique)" is uniqueness of the maximizer of
(10), per §4's opening, p.15; for `Λ` it is uniqueness of the distorted law. -/
theorem theorem_2 (P : Params) :
    (∀ (μ : ℝ) (s c : ℝ≥0), V P μ s c = ((vClosed P μ s c : ℝ) : EReal)) ∧
    IsBDPSolution P (vClosed P) ∧
    (∀ (μ : ℝ) (s c : ℝ≥0), 0 < c →
      IsDistortion μ s (qStar P s c) (Gstar P μ s c) ∧
      klDiv (Gstar P μ s c) (baseLaw μ s (qStar P s c)) ≠ ∞ ∧
      bdpObjective P (vClosed P) μ s c (qStar P s c) (Gstar P μ s c) = vClosed P μ s c ∧
      meanVar s (qStar P s c) = s - sTH P c ∧
      (∀ (q : ℝ≥0) (G : Measure ℝ), IsDistortion μ s q G → klDiv G (baseLaw μ s q) ≠ ∞ →
        bdpObjective P (vClosed P) μ s c q G = vClosed P μ s c →
          q = qStar P s c ∧ G = Gstar P μ s c) ∧
      Gstar P μ s c = gaussianReal (μ + boost P s c) (meanVar s (qStar P s c))) ∧
    (∀ (μ₀ : ℝ) (s₀ c₁ : ℝ≥0), 0 < c₁ → 0 < P.η →
      ∃ M : Policy s₀, IsOptimalPolicy P c₁ M ∧ IsAdmissible M μ₀ ∧
        totalValue P M μ₀ c₁ = V P μ₀ s₀ c₁ ∧
        Tendsto (horizonValue P M μ₀ c₁) atTop (𝓝 ((vClosed P μ₀ s₀ c₁ : ℝ) : EReal))) := by sorry

end LearnManip
