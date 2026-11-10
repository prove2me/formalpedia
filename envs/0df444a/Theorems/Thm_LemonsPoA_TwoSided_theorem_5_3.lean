-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_theorem_5_3
-- name    : LemonsPoA.TwoSided.theorem_5_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:12:45.29338+00:00
-- url     : https://prove2.me/theorems/9eddfbf7-fca0-4842-8941-a63ecb5760b4
-- title:
--   Theorem 5.3 — every sequential equilibrium of the seller-proposer mechanism attains $W^-_S(I)\ge\frac{(\pi^-)^2\pi^+}{4e}\sqrt{1+\rho}$
-- statement:
--   Let $I=(v,G,F,\Sigma_S,\Sigma_B)$ be a market instance: i.i.d. types $\theta_S,\theta_B\sim G$ on a measurable type space, affine values $v(c,\theta)=c\,x(\theta)+y(\theta)$ with $x\ge 0$, a common component and finite signals $(C,\Sigma_S,\Sigma_B)$ with an arbitrary joint law independent of the types, and the news ordering (13)-(14). Let $\sigma^-_S$ be the most pessimistic seller signal and $\sigma^+_B$ the most optimistic buyer signal (41). Suppose $I$ is $(\pi^-,\pi^+,\rho)$-regular (Definition 5.2): $C\ge 0$ is dominated in convex order by an exponential variable of mean $\mu=E[C]\in(0,\infty)$; $\Pr[\Sigma_S=\sigma^-_S\mid\Sigma_B=\sigma_B]\ge\pi^->0$ for all $\sigma_B$; $\Pr[\Sigma_B=\sigma^+_B\mid\Sigma_S=\sigma_S]\ge\pi^+>0$ for all $\sigma_S$; $(x(\theta),y(\theta))$ is log-concave with $E[x(\theta)+|y(\theta)|]<\infty$; and $\mathrm{Corr}(x(\theta),y(\theta))\ge\rho>-1$. Then, in the seller-proposer game, the worst-case fraction of first-best gains from trade over all sequential equilibria, in the fine-menu limit,
--   $$W^-_S(I)=\inf_{(Q_n)\ \text{fine}}\ \liminf_{n\to\infty}\ \inf_{(p,a,\lambda)\in E_S(I,Q_n)}W_S(p,a,\lambda)$$
--   satisfies
--   $$W^-_S(I)\ \ge\ \frac{(\pi^-)^2\pi^+}{4e}\sqrt{1+\rho}.$$
--
--   This is the paper's main price-of-anarchy bound for the seller-proposer mechanism with two-sided information: it holds for every sequential equilibrium, uniformly over instances with the stated regularity.
--
--   **Formalization Note** $W^-_S$ is computed in `EReal`. $FB>0$ is not a hypothesis: it follows from Definition 5.2 (INSIGHTS I2).
--
--   Differences from the source:
--   - encoding: joint law of $(C,\Sigma_S,\Sigma_B)$ on $\mathbb R\times S_S\times S_B$, independent of the i.i.d. types $\theta_S,\theta_B\sim G$ → finite measures $F(\sigma_S,\sigma_B)(A)=\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ of total mass $1$; expectations against $F(\sigma_S,\sigma_B)\otimes G\otimes G$ summed over signal pairs; reason: every law on $\mathbb R\times S_S\times S_B$ with finite $S_S,S_B$ is uniquely of this form; same instances
--   - reading: conditional probabilities, $m(\sigma_S,\sigma_B)$, the news ordering (13)-(14), equilibrium conditions 1-4 and Definition 5.2 items 2-3 for all signals → only for signals (and signal pairs) of positive probability; reason: these quantities are undefined on null events; Definition 1.4 writes $\sigma_B\in\mathrm{supp}\,\Sigma_B$
--   - reading: $\sigma^-_S\in\arg\min m(\cdot,\sigma^*_B)$, $\sigma^+_B\in\arg\max m(\sigma^*_S,\cdot)$ simultaneously for all partner signals (41) → universally quantified $\sigma^-_S,\sigma^+_B$ with hypotheses `IsPessimistic`, `IsOptimistic` (extremal among pairs of positive probability); reason: the statement then holds for every admissible choice, ties included, which covers the paper's fixed choice
--   - reading: (21): off-path beliefs are limits along trembles $\ell^n$, "for all $\sigma_P$, $\sigma_R$, and $q$" → one tremble sequence $\ell^n$ (strictly positive, summing to 1 over $Q\cup\{\bot\}$, converging to $\ell$) serves every off-path $(\sigma_B,q)$; reason: Kreps-Wilson consistency, which the paper cites; the stronger requirement on the equilibrium
--   - encoding: $W^-_S(I,Q)=\inf_{E_S(I,Q)}W_S$ and $W^-_S(I)=\inf_{\text{fine}}\liminf_n W^-_S(I,Q_n)$ → infimum and liminf in `EReal` ($\inf\emptyset=+\infty$); reason: the paper's extended-real infimum; avoids the real `sInf ∅ = 0`
--   - encoding: finite menu $Q\subset\mathbb R$, $\mathcal Q=Q\cup\{\bot\}$, strategies of a continuous type space → `Q : Finset ℝ`, exit as `Option.none`, strategies and acceptance probabilities measurable in $\theta$ and $\mathbb R$-valued in $[0,1]$; reason: Lean conventions; measurability is the standing convention that makes the expectations in (16)-(22) defined
--   - reading: Definition 5.2 item 4: "$(x(\theta),y(\theta))$ has a log-concave density" → `LogConcavePrefs`: a joint log-concave Lebesgue density, or $x$ a.s. constant and $y$ with a log-concave density, or $y$ a.s. constant and $x$ with a log-concave density; reason: item 5 provides for a constant coordinate, which item 4 as printed excludes; Definition 1.4 item 1 (p. 10) states the clause (INSIGHTS I1)
--   - encoding: for any convex $\varphi:\mathbb R\to\mathbb R$, $E[\varphi(C)]\le E[\varphi(Z)]$ → for every convex $\varphi$ with $\varphi(Z)$ integrable, $\varphi(C)$ is integrable and $E[\varphi(C)]\le E[\varphi(Z)]$ (Bochner integrals); reason: same condition: for convex $\varphi$ and integrable $C,Z$ both sides lie in $(-\infty,+\infty]$, and the inequality is trivial when $E[\varphi(Z)]=+\infty$; avoids the junk value 0 of a non-integrable integral
--   - generalization: item 5: $\mathrm{Corr}(x,y)\ge\rho>-1$; "if either $x(\theta)$ or $y(\theta)$ is constant, then take this to be satisfied for $\rho=0$" → $-1<\rho\le\mathrm{Cov}(x,y)/(\sqrt{\mathrm{Var}\,x}\sqrt{\mathrm{Var}\,y})$ with the plain quotient, which is $0$ for a constant coordinate, so the condition reads $\rho\le 0$ there; reason: the paper's constant-coordinate case $\rho=0$ is included; allowing $-1<\rho<0$ adds instances. For (46) and (47) the conclusion is independent of $\rho$; for (40), (48), and Theorem 5.3 the bounds follow from the $\rho=0$ case by monotonicity (both sides of the second inequality in (48) share the positive factor $\sqrt{1+\rho}$)
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 28, Theorem 5.3

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Game
import Definitions.Def_LemonsPoA_TwoSided_Regular

namespace LemonsPoA.TwoSided

/-- Theorem 5.3 (p. 28): for every `(π⁻, π⁺, ρ)`-regular market instance in which the seller
proposes, `W⁻_S(I) ≥ ((π⁻)² π⁺ / (4e)) √(1 + ρ)`. -/
theorem theorem_5_3 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hnews : M.NewsOrdered)
    (σm : SS) (σp : SB) (hσm : M.IsPessimistic σm) (hσp : M.IsOptimistic σp)
    (πm πp ρ : ℝ) (hreg : M.Regular σm σp πm πp ρ) :
    ((πm ^ 2 * πp / (4 * Real.exp 1) * Real.sqrt (1 + ρ) : ℝ) : EReal) ≤ M.Wminus := by sorry

end LemonsPoA.TwoSided
