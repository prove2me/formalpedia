-- Prove2me | Theorems.Thm_MarketplaceLeakage_Communication_piL_deriv
-- name    : MarketplaceLeakage.Communication.piL_deriv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:46:20.213353+00:00
-- url     : https://prove2.me/theorems/bfafd593-fd94-482a-a9ca-52f66a2d437a
-- title:
--   §8.4, p. 38 — dΠ_L/dη = −((1 − q)qv/(1 − η)²)((2 − η)qη + 2(1 − η)²) + c(1 − q), and Π_L is decreasing when qv > c
-- statement:
--   Let $c<v$ and $0<q<1$, and consider $\Pi_L(\eta)=(1-\eta+\eta q)\bigl(\frac{(1-(2-q)\eta)qv}{1-\eta}-c\bigr)$ as a function of $\eta$.
--
--   1. For every $\eta<1$, $\Pi_L$ is differentiable at $\eta$ with
--   $$\frac{d\Pi_L}{d\eta}=-\frac{(1-q)\,qv}{(1-\eta)^2}\Bigl((2-\eta)q\eta+2(1-\eta)^2\Bigr)+c(1-q).$$
--   2. If moreover $v>0$ and $qv>c$, then $\Pi_L$ is strictly decreasing on $[0,1)$.
--
--   Together with the obvious monotonicity of $\Pi_H(\eta)=\eta q(v-c)$, this shows that the two options available to the marketplace under a ban react in opposite directions to the information loss $1-\eta$.
--
--   **Formalization Note.** Part 2 adds $v>0$, which the page uses without stating it (it reads the derivative's first term as at most $-(1-q)qv$). For $v\le 0$ the claim is false: with $v=-1$, $c=-2$, $q=1/2$ one has $\Pi_L(0)=1.5<\Pi_L(0.9)\approx 2.06$.
-- source:
--   Hagiu, Wright, Marketplace Leakage, authors' manuscript dated March 2023 (sha256 cb89c…98a6; published in Management Science, doi:10.1287/mnsc.2023.4757), p. 38, §8.4, Proof of Proposition 3, display dΠ_L/dη

import Mathlib
import Definitions.Def_MarketplaceLeakage_Communication_Setting

namespace MarketplaceLeakage.Communication

theorem piL_deriv (v c : ℝ) (hvc : c < v) (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    (∀ η : ℝ, η < 1 →
      HasDerivAt (PiL v c q)
        (-((1 - q) * q * v / (1 - η) ^ 2) * ((2 - η) * q * η + 2 * (1 - η) ^ 2) + c * (1 - q)) η) ∧
    (0 < v → c < q * v → StrictAntiOn (PiL v c q) (Set.Ico 0 1)) := by sorry

end MarketplaceLeakage.Communication
