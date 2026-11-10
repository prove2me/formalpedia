-- Prove2me | Theorems.Thm_LemonsPoA_TwoSided_eq_48
-- name    : LemonsPoA.TwoSided.eq_48
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:12:38.568644+00:00
-- url     : https://prove2.me/theorems/502759c8-2902-4603-8b84-76b0162d5c4c
-- title:
--   §5.2, Eq. (48) — $\frac{R}{FB}\ge\frac{\pi^-}4\sqrt{1+\rho}$
-- statement:
--   Let $I$ be a market instance with the news ordering, most pessimistic seller signal $\sigma^-_S$ and most optimistic buyer signal $\sigma^+_B$, $(\pi^-,\pi^+,\rho)$-regular (Definition 5.2); let $d=m(\sigma^-_S,\sigma^+_B)$, $\mu=E[C]$, and $R=E[(\hat v_B-\hat v_S)_+]$ with $\hat v=d\,x+y$. Then
--   $$\frac{R}{FB}\ \ge\ \frac{\sqrt{1+\rho}}{2}\cdot\frac{d\sqrt{\mathrm{Var}(x(\theta))}+\sqrt{\mathrm{Var}(y(\theta))}}{\mu\sqrt{\mathrm{Var}(x(\theta))}+\sqrt{\mathrm{Var}(y(\theta))}}\ \ge\ \frac{\pi^-}{4}\sqrt{1+\rho}.$$
--
--   The belief-robust market retains a constant fraction of the original first-best.
--
--   **Formalization Note** $FB>0$ and the positivity of the denominator are not assumed: they follow from Definition 5.2 (INSIGHTS I2).
--
--   Differences from the source:
--   - reading: conditional probabilities, $m(\sigma_S,\sigma_B)$, the news ordering (13)-(14), equilibrium conditions 1-4 and Definition 5.2 items 2-3 for all signals → only for signals (and signal pairs) of positive probability; reason: these quantities are undefined on null events; Definition 1.4 writes $\sigma_B\in\mathrm{supp}\,\Sigma_B$
--   - reading: $\sigma^-_S\in\arg\min m(\cdot,\sigma^*_B)$, $\sigma^+_B\in\arg\max m(\sigma^*_S,\cdot)$ simultaneously for all partner signals (41) → universally quantified $\sigma^-_S,\sigma^+_B$ with hypotheses `IsPessimistic`, `IsOptimistic` (extremal among pairs of positive probability); reason: the statement then holds for every admissible choice, ties included, which covers the paper's fixed choice
--   - reading: Definition 5.2 item 4: "$(x(\theta),y(\theta))$ has a log-concave density" → `LogConcavePrefs`: a joint log-concave Lebesgue density, or $x$ a.s. constant and $y$ with a log-concave density, or $y$ a.s. constant and $x$ with a log-concave density; reason: item 5 provides for a constant coordinate, which item 4 as printed excludes; Definition 1.4 item 1 (p. 10) states the clause (INSIGHTS I1)
--   - encoding: for any convex $\varphi:\mathbb R\to\mathbb R$, $E[\varphi(C)]\le E[\varphi(Z)]$ → for every convex $\varphi$ with $\varphi(Z)$ integrable, $\varphi(C)$ is integrable and $E[\varphi(C)]\le E[\varphi(Z)]$ (Bochner integrals); reason: same condition: for convex $\varphi$ and integrable $C,Z$ both sides lie in $(-\infty,+\infty]$, and the inequality is trivial when $E[\varphi(Z)]=+\infty$; avoids the junk value 0 of a non-integrable integral
--   - generalization: item 5: $\mathrm{Corr}(x,y)\ge\rho>-1$; "if either $x(\theta)$ or $y(\theta)$ is constant, then take this to be satisfied for $\rho=0$" → $-1<\rho\le\mathrm{Cov}(x,y)/(\sqrt{\mathrm{Var}\,x}\sqrt{\mathrm{Var}\,y})$ with the plain quotient, which is $0$ for a constant coordinate, so the condition reads $\rho\le 0$ there; reason: the paper's constant-coordinate case $\rho=0$ is included; allowing $-1<\rho<0$ adds instances. For (46) and (47) the conclusion is independent of $\rho$; for (40), (48), and Theorem 5.3 the bounds follow from the $\rho=0$ case by monotonicity (both sides of the second inequality in (48) share the positive factor $\sqrt{1+\rho}$)
--   - encoding: joint law of $(C,\Sigma_S,\Sigma_B)$ on $\mathbb R\times S_S\times S_B$, independent of the i.i.d. types $\theta_S,\theta_B\sim G$ → finite measures $F(\sigma_S,\sigma_B)(A)=\Pr[C\in A,\Sigma_S=\sigma_S,\Sigma_B=\sigma_B]$ of total mass $1$; expectations against $F(\sigma_S,\sigma_B)\otimes G\otimes G$ summed over signal pairs; reason: every law on $\mathbb R\times S_S\times S_B$ with finite $S_S,S_B$ is uniquely of this form; same instances
-- source:
--   Durvasula, Roughgarden, The Price of Anarchy in Markets for Lemons, STOC 2027 submission (manuscript sha256 5a158b50…), p. 28, §5.2, Eq. (48) (in the proof of Theorem 5.3)

import Mathlib
import Definitions.Def_LemonsPoA_TwoSided_Market
import Definitions.Def_LemonsPoA_TwoSided_Regular

open ProbabilityTheory

namespace LemonsPoA.TwoSided

/-- §5.2, Eq. (48) (p. 28): under Definition 5.2, with `d = m(σ⁻_S, σ⁺_B)`,
`R/FB ≥ (√(1+ρ)/2) (d √Var x + √Var y)/(µ √Var x + √Var y) ≥ (π⁻/4) √(1+ρ)`. -/
theorem eq_48 {Θ : Type*} [MeasurableSpace Θ] {SS SB : Type*} [Fintype SS] [Fintype SB]
    (M : Market Θ SS SB) (hnews : M.NewsOrdered)
    (σm : SS) (σp : SB) (hσm : M.IsPessimistic σm) (hσp : M.IsOptimistic σp)
    (πm πp ρ : ℝ) (hreg : M.Regular σm σp πm πp ρ) :
    Real.sqrt (1 + ρ) / 2 *
          ((M.m σm σp * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G)) /
            (M.meanC * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G))) ≤
        M.R (M.m σm σp) / M.FB ∧
      πm / 4 * Real.sqrt (1 + ρ) ≤
        Real.sqrt (1 + ρ) / 2 *
          ((M.m σm σp * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G)) /
            (M.meanC * Real.sqrt (variance M.x M.G) + Real.sqrt (variance M.y M.G))) := by sorry

end LemonsPoA.TwoSided
