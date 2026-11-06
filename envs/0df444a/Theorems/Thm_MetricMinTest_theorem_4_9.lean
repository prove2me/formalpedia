-- Prove2me | Theorems.Thm_MetricMinTest_theorem_4_9
-- name    : MetricMinTest.theorem_4_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:12:30.265174+00:00
-- url     : https://prove2.me/theorems/bf68955c-1c19-4885-bfc7-bd3f921faa3a
-- title:
--   Theorem 4.9, p.12 — nonadaptive cost at the critical exponent is $\Theta_b(F+HL)$
-- statement:
--   Let $b\ge2$, $m\ge1$, $\gamma\in(0,1/4]$, $\delta\in(0,1/5]$, $d=d_{b,1/2,m}$, $F=F_d(\gamma)$, $H=H_d(\gamma)$, $L=\ln(1/\delta)$, $k=b^m$.
--   1. Every $(\gamma,\delta)$-valid nonadaptive tester satisfies $\Pr_\xi[N(\xi)\le F/256]\le4.5\,\delta$.
--   2. Consequently
--   $$\max\Big\{\frac F{256},\frac{HL}8\Big\}\le B^{\mathrm{na}}_d(\gamma,\delta)\le\frac{24b\ln b}{b-1}F+24HL+1,$$
--   and, if $\delta\le1/10$, also $C^{\mathrm{na}}_d(\gamma,\delta)\ge\max\{F/512,HL/8\}$.
--   3. Hence, for each $b\ge2$ there are $c,C>0$ depending only on $b$ such that for all $m\ge1$, $\gamma\in(0,1/4]$, $\delta\in(0,1/10]$: $c(F+HL)\le C^{\mathrm{na}}_d\le B^{\mathrm{na}}_d\le C(F+HL)$ and $cH\ln(k/\delta)\le F+HL\le CH\ln(k/\delta)$.
--   4. On $d_m$ ($b=4$) the upper bound is at most $45F+24HL$.
--
--   **Formalization Note** Nonadaptive testers are valid one-round testers.
--
--   Differences from the source:
--   - encoding: $\Theta_b$ → constants $c,C>0$ chosen after $b$ and before $m,\gamma,\delta$; reason: quantifier form of $\Theta_b$
--   - reading: "$C^{\mathrm{na}}_d$ and $B^{\mathrm{na}}_d$ are both $\Theta_b(F+HL)$" → lower bound on $C^{\mathrm{na}}$, $C^{\mathrm{na}}\le B^{\mathrm{na}}$, upper bound on $B^{\mathrm{na}}$; reason: equivalent given $C^{\mathrm{na}}\le B^{\mathrm{na}}$, which the paper states on p.9
--   - encoding: "on $d_m$ the upper bound is at most $45F+24HL$" → the case $b=4$ of the displayed upper bound; reason: $d_m=d_{4,1/2,m}$
--   - encoding: nonadaptive tester → valid one-round tester; reason: Lean model, Definition C.6
--   - encoding: the minima $H_d(\gamma)$ of (1.1) and $F_d(\gamma)$ of (2.1) over indexed balls $B_{j\ell}$ → real infima of the feasible values, with indexed balls encoded by the pairs $(j,i)$ with $d(j,i)<\gamma$; reason: the minima are attained (pp.6–7) and a repeated distance only duplicates a ball at equal cost, so the values are the same
--   - encoding: $N(\xi)<\infty$ almost surely → $\mathbb N$-valued counts for every $\xi$, with the acceptance set and the cost measurable inside validity; reason: a tester with $N(\xi)=\infty$ on a null set can be changed there without changing any law or expectation, and the probabilities and expectations on the page presuppose measurability
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem 4.9, p.12

import Mathlib
import Definitions.Def_MetricMinTest_geomMetric
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Cna
import Definitions.Def_MetricMinTest_Bna

namespace MetricMinTest

open MeasureTheory

/-- **Theorem 4.9 (Nonadaptive lower bound at the critical exponent).** Chen–Fang, *Minimum-Mean
Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb),
Theorem 4.9, p.12: "Let b ≥ 2, m ≥ 1, γ ∈ (0, 1/4], and δ ∈ (0, 1/5], and let d = d_{b,1/2,m}.
Every (γ, δ)-valid nonadaptive tester satisfies Pr_ξ[N(ξ) ≤ F/256] ≤ 4.5δ. Consequently
max{F/256, HL/8} ≤ B^na_d(γ, δ) ≤ (24 b ln b/(b − 1))F + 24HL + 1, and, if δ ≤ 1/10, also
C^na_d(γ, δ) ≥ max{F/512, HL/8}. Hence C^na_d(γ, δ) and B^na_d(γ, δ) are both
Θ_b(F + HL) = Θ_b(H ln(k/δ)) for δ ≤ 1/10. On d_m the upper bound is at most 45F + 24HL."

**Formalization Note.** `F = F_d(γ)`, `H = H_d(γ)`, `L = ln(1/δ)`, `k = b^m`, points
`Fin m → Fin b`, nonadaptive testers valid `RoundTester _ 1`. The first block is the theorem's
first two sentences; it ends with the last sentence (`b = 4`, `d_m = d_{4,1/2,m}`): the printed
upper bound is at most `45F + 24HL`. The second block is the `Θ_b` sentence: for each `b ≥ 2`,
constants `c, C > 0` depending only on `b` (chosen before `m, γ, δ`), with `C^na ≤ B^na`
stated explicitly so that both measures are bracketed. -/
theorem theorem_4_9 :
    (∀ b m : ℕ, 2 ≤ b → 1 ≤ m → ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
      δ ∈ Set.Ioc (0 : ℝ) (1 / 5) →
      (∀ A : RoundTester (Fin m → Fin b) 1, A.IsValid (geomMetric b m (1 / 2) γ) γ δ →
        A.μξ {ξ | (A.naCost ξ : ℝ) ≤ certWorkload (geomMetric b m (1 / 2) γ) γ / 256} ≤
          ENNReal.ofReal (4.5 * δ)) ∧
      ENNReal.ofReal (max (certWorkload (geomMetric b m (1 / 2) γ) γ / 256)
          (infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) / 8)) ≤
        Bna (geomMetric b m (1 / 2) γ) γ δ ∧
      Bna (geomMetric b m (1 / 2) γ) γ δ ≤
        ENNReal.ofReal (24 * b * Real.log b / ((b : ℝ) - 1) *
            certWorkload (geomMetric b m (1 / 2) γ) γ +
          24 * infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) + 1) ∧
      (δ ≤ 1 / 10 →
        ENNReal.ofReal (max (certWorkload (geomMetric b m (1 / 2) γ) γ / 512)
            (infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) / 8)) ≤
          Cna (geomMetric b m (1 / 2) γ) γ δ) ∧
      (b = 4 →
        24 * b * Real.log b / ((b : ℝ) - 1) * certWorkload (geomMetric b m (1 / 2) γ) γ +
            24 * infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) + 1 ≤
          45 * certWorkload (geomMetric b m (1 / 2) γ) γ +
            24 * infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ))) ∧
    (∀ b : ℕ, 2 ≤ b → ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ m : ℕ, 1 ≤ m → ∀ γ δ : ℝ,
      γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 10) →
      ENNReal.ofReal (c * (certWorkload (geomMetric b m (1 / 2) γ) γ +
          infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ))) ≤
        Cna (geomMetric b m (1 / 2) γ) γ δ ∧
      Cna (geomMetric b m (1 / 2) γ) γ δ ≤ Bna (geomMetric b m (1 / 2) γ) γ δ ∧
      Bna (geomMetric b m (1 / 2) γ) γ δ ≤
        ENNReal.ofReal (C * (certWorkload (geomMetric b m (1 / 2) γ) γ +
          infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ))) ∧
      c * (infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log ((b : ℝ) ^ m / δ)) ≤
        certWorkload (geomMetric b m (1 / 2) γ) γ +
          infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) ∧
      certWorkload (geomMetric b m (1 / 2) γ) γ +
          infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log (1 / δ) ≤
        C * (infoWorkload (geomMetric b m (1 / 2) γ) γ * Real.log ((b : ℝ) ^ m / δ))) := by sorry

end MetricMinTest
