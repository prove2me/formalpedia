-- Prove2me | Theorems.Thm_GDPRDataMarkets_Rights_proposition_1
-- name    : GDPRDataMarkets.Rights.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:00:12.360427+00:00
-- url     : https://prove2.me/theorems/266e8f23-5c67-4e9a-996a-ae3b6a1558c7
-- title:
--   Proposition 1 — with privacy rights the monopoly equilibrium in the four regimes c ≤ δσ/2, ≤ δσ/√2, < δσ, ≥ δσ
-- statement:
--   Consider the two-period monopoly market with privacy rights, under $\kappa_H>\kappa_L>0$, $\delta\in(0,1]$, $c\ge0$ and Assumption 1, $\mu\ge\max\{(3+\delta)\sigma,\ \tfrac12+(2+\delta)\sigma\}$. Write $p^*_{1M}$ for the equilibrium first-period price, $p^*_{2M}$ for the equilibrium second-period basic price and $r^*_M(v)$ for the equilibrium personalized price. In each of the following regimes there is an equilibrium with the stated outcome.
--
--   **A.** If $0\le c\le\delta\sigma/2$: $p^*_{1M}=P_1^*$ and $p^*_{2M}=1$ (no basic good is sold in period 2).
--   1. Consumers with $v\ge v_1^*$ purchase and opt in in period 1; in period 2 both types keep their data and buy the personalized good at $r^*_M(v)=(1+\mu-\sigma)v-c$.
--   2. Consumers with $v<v_1^*$ purchase in neither period.
--
--   **B.** If $\delta\sigma/2<c\le\delta\sigma/\sqrt2$: $p^*_{1M}=1/2$ and $p^*_{2M}=1$ (no basic good is sold in period 2).
--   1. Consumers with $v\ge c/(\delta\sigma)$ purchase and opt in; in period 2 both types buy the personalized good at $r^*_M(v)=(1+\mu-\sigma)v-c$.
--   2. Consumers with $1/2\le v<c/(\delta\sigma)$ purchase without opting in, and make no purchase in period 2.
--   3. Consumers with $v<1/2$ purchase in neither period.
--
--   **C.** If $\delta\sigma/\sqrt2<c<\delta\sigma$: $p^*_{1M}=p^*_{2M}=1/2$.
--   1. Consumers with $v\ge c/(\delta\sigma)$ purchase and opt in; in period 2 both types buy the personalized good at $r^*_M(v)=(\mu-\sigma)v+1/2-c$.
--   2. Consumers with $1/2\le v<c/(\delta\sigma)$ purchase without opting in, and buy the basic good at $1/2$ in period 2.
--   3. Consumers with $v<1/2$ purchase in neither period.
--
--   **D.** If $c\ge\delta\sigma$: no consumer opts in, $p^*_{1M}=p^*_{2M}=1/2$, and a consumer purchases in each period iff $v\ge1/2$.
--
--   Here
--   $$v_1^*=\max\Big\{\frac{1+\delta\sigma+(1+\delta)c}{2+\delta+\delta\mu+\delta\sigma},\frac{c}{\delta\sigma}\Big\},\qquad P_1^*=\max\Big\{\frac{(1+\delta\sigma)^2-(1+\delta\mu-\delta^2\sigma)c}{2+\delta+\delta\mu+\delta\sigma},\frac{c}{\delta\sigma}\Big\}.$$
--
--   The proposition shows how the breach cost shapes data collection under GDPR-style rights: at low $c$ every buyer opts in; at intermediate $c$ only high-valuation consumers opt in, and the firm drops the basic good in period 2 unless the opted-out segment is large; once $c\ge\delta\sigma$ no one shares data.
--
--   **Formalization Note** An equilibrium requires optimality at every history: of each personalized price at every basic price, of the basic price after every first-period price, of every consumer's action after every first-period price, and of the first-period price over all reals. Profits are integrals over the consumers' own choices. The paper does not claim uniqueness, and the theorem asserts existence only. "No basic good is offered" is encoded as $p^*_{2M}=1$, the price the paper names in eq. (3). In case B(i) the printed SSRN text gives $r^*_M(v)=(\mu-\sigma)v+1/2-c$, which is case C's price; since no basic good is sold in B, eq. (2) gives $(1+\mu-\sigma)v-c$, and the theorem states that price. The knife-edge $c=\delta\sigma/\sqrt2$ is assigned to B, as in the proposition (the appendix puts it in its case 1, i.e. C; both outcomes are equilibria there).
-- source:
--   Ke, Sudhir, Privacy Rights and Data Security: GDPR and Personal Data Markets, SSRN 3643979 (pdfTeX build 2022-09-14), pp. 15–16, Proposition 1

import Mathlib
import Definitions.Def_GDPRDataMarkets_Rights_Model
import Definitions.Def_GDPRDataMarkets_Rights_ClosedForms

namespace GDPRDataMarkets.Rights

/-- Proposition 1, pp. 15–16: in the monopoly market with privacy rights, under Assumption 1, an
equilibrium exists with the following outcome in each of the four regimes of the breach cost `c`
(`q*` is the equilibrium basic price `p*_2M = s.p2 s.p1`). -/
theorem proposition_1 (P : Params) (hS : P.Standing) (hA : P.Assumption1) :
    -- A. `0 ≤ c ≤ δσ/2`
    (P.c ≤ P.d * P.sigma / 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = P1star P ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v1star P ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < v1star P →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- B. `δσ/2 < c ≤ δσ/√2`
    (P.d * P.sigma / 2 < P.c ∧ P.c ≤ P.d * P.sigma / Real.sqrt 2 →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (1 + P.mu - P.sigma) * v - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ v < s.p2 s.p1) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- C. `δσ/√2 < c < δσ`
    (P.d * P.sigma / Real.sqrt 2 < P.c ∧ P.c < P.d * P.sigma →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, P.c / (P.d * P.sigma) ≤ v →
          s.choice s.p1 v = .optIn ∧
          keeps P v P.kL (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          keeps P v P.kH (s.p2 s.p1) (s.r v (s.p2 s.p1)) ∧
          s.r v (s.p2 s.p1) = (P.mu - P.sigma) * v + 1 / 2 - P.c) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, 1 / 2 ≤ v → v < P.c / (P.d * P.sigma) →
          s.choice s.p1 v = .buy ∧ s.p2 s.p1 ≤ v) ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1, v < 1 / 2 →
          s.choice s.p1 v = .none ∧ v < s.p2 s.p1)) ∧
    -- D. `c ≥ δσ`
    (P.d * P.sigma ≤ P.c →
      ∃ s : Profile, IsEquilibrium P s ∧ s.p1 = 1 / 2 ∧ s.p2 s.p1 = 1 / 2 ∧
        (∀ v ∈ Set.Icc (0 : ℝ) 1,
          s.choice s.p1 v ≠ .optIn ∧
          (s.choice s.p1 v = .buy ↔ 1 / 2 ≤ v) ∧
          (s.p2 s.p1 ≤ v ↔ 1 / 2 ≤ v))) := by sorry

end GDPRDataMarkets.Rights
