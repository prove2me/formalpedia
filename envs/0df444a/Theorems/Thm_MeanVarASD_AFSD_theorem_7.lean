-- Prove2me | Theorems.Thm_MeanVarASD_AFSD_theorem_7
-- name    : MeanVarASD.AFSD.theorem_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:40.400053+00:00
-- url     : https://prove2.me/theorems/5bacab28-b5e0-43d0-a742-bbf69a7bc541
-- title:
--   Theorem 7, p. 6 — if µY > µX then X ≤_(1+γ,1+γ) Y for all γ ≥ 1/(1 + 2t(t + √(t²+1))), t = (µY − µX)/(σY + σX)
-- statement:
--   Let $X$ and $Y$ be random variables with finite variances, means $\mu_X=\mathbb E X$, $\mu_Y=\mathbb E Y$ and standard deviations $\sigma_X=\sqrt{\mathbb V(X)}$, $\sigma_Y=\sqrt{\mathbb V(Y)}$, and suppose $\mu_Y>\mu_X$. Define
--   $$t=\frac{\mu_Y-\mu_X}{\sigma_Y+\sigma_X},\qquad \gamma^*=\frac{1}{1+2t\big(t+\sqrt{t^2+1}\big)}.$$
--   Then for every $\gamma$ with $\gamma^*\le\gamma\le1$,
--   $$X\le_{(1+\gamma,1+\gamma)}Y,$$
--   that is, $\mathbb E\,u(X)\le\mathbb E\,u(Y)$ (both expectations finite) for every continuously differentiable $u$ with $0\le\gamma u'(y)\le u'(x)$ and $0\le\gamma u'(x)\le u'(y)$ for all $x\le y$.
--
--   In words: whenever the standardized mean difference $t$ is large enough that $\gamma\ge\gamma^*$, every decision maker whose marginal utilities differ at most by the factor $1/\gamma$ prefers $Y$ to $X$, whatever the distributions of $X$ and $Y$ beyond their means and variances. This is a distribution-free sufficient condition for $\varepsilon$-almost first-order stochastic dominance with $\varepsilon=\gamma/(1+\gamma)$.
--
--   **Formalization Note** $X$ and $Y$ are square-integrable (`MemLp · 2`) on one probability space; $\sigma_X$, $\sigma_Y$ are the square roots of Mathlib's `variance`, not free reals. The bound $\gamma\le1$ is the domain of the order in Definition 1(b), not an added restriction; $\gamma\ge0$ follows from $\gamma^*>0$. If $\sigma_X=\sigma_Y=0$ the paper's $t$ is undefined; Lean's convention gives $t=0$ and $\gamma^*=1$, and the statement then asserts dominance for the increasing affine utilities only, which is true. No hypothesis is added for this corner.
-- source:
--   Müller, Scarsini, Tsetlin & Winkler, Ranking distributions when only means and variances are known, INSEAD Working Paper 2020/36/DSC (31 July 2020; SSRN 3440103), p. 6 (PDF 7), Theorem 7

import Mathlib
import Definitions.Def_MeanVarASD_AFSD_Defs

namespace MeanVarASD.AFSD

open MeasureTheory ProbabilityTheory

/-- Theorem 7, p. 6: let `X, Y` be square-integrable with means `µX < µY` and standard
deviations `σX, σY`, and `t = (µY − µX)/(σY + σX)`. Then `X ≤_(1+γ,1+γ) Y` for every
`γ` with `γ* = 1/(1 + 2t(t + √(t² + 1))) ≤ γ ≤ 1` (the order is defined for `γ ≤ 1`). -/
theorem theorem_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ) (hX : MemLp X 2 P) (hY : MemLp Y 2 P)
    (hμ : ∫ ω, X ω ∂P < ∫ ω, Y ω ∂P) (γ : ℝ)
    (hγ : gammaStar (tStat (∫ ω, X ω ∂P) (∫ ω, Y ω ∂P)
            (Real.sqrt (variance X P)) (Real.sqrt (variance Y P))) ≤ γ)
    (hγ1 : γ ≤ 1) :
    SDle γ γ P X Y := by sorry

end MeanVarASD.AFSD
