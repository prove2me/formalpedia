-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_D
-- name    : MetricMinTest.Supplement.theorem_D
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:40:56.723223+00:00
-- url     : https://prove2.me/theorems/4317d793-5337-442a-9abc-23b63addf85e
-- title:
--   Theorem D, p.3 — the price of local thresholds: $H\le F\le(2+2\ln(2\gamma^2H))H$, $B^\star=O(FL)$, attained on $d_m$; randomized designs pay $pF$
-- statement:
--   Let $d$ be a finite metric or pseudometric, $\gamma,\delta\in(0,1/4]$, $L=\ln(1/\delta)$, $H=H_d(\gamma)$ and $F=F_d(\gamma)$. Then
--   $$H\le F\le\big(2+2\ln(2\gamma^2H)\big)H,\qquad B^\star_d(\gamma,\delta)=O(FL).$$
--   The logarithmic conversion factor is attained on the critical ultrametric $d_m$: there is an absolute $c>0$ with $F_{d_m}(\gamma)\ge c\,(2+2\ln(2\gamma^2H_{d_m}(\gamma)))H_{d_m}(\gamma)$ for all $m\ge1$ and $\gamma\in(0,1/4]$. Finally, for $p\in(0,1]$, if a randomized ball design (a random family $S$ of eligible balls $B(j,r)$, $r<\gamma$, with arbitrary correlations) covers every fixed index with probability at least $p$, then its expected geometric cost satisfies
--   $$\mathbb E\sum_{(j,r)\in S}(\gamma-r)^{-2}\ge p\,F .$$
--
--   Local threshold certificates thus lose at most a logarithmic factor against the information workload, this loss is unavoidable on $d_m$, and randomizing the choice of certificates does not avoid it.
--
--   **Formalization Note** A design is a probability mass function on finite sets of pairs $(j,i)$ with $d(j,i)<\gamma$ (the ball $B(j,d(j,i))$).
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - encoding: $O(FL)$ → explicit constants $c,C>0$ quantified before every variable they must not depend on; reason: the paper's convention for $\asymp$, $O$, $\Theta$, $\Omega$ (§2, p.6)
--   - reading: the logarithmic conversion factor is attained on $d_m$ → an absolute $c>0$ with $F_{d_m}\ge c(2+2\ln(2\gamma^2H_{d_m}))H_{d_m}$ for all $m\ge1$, $\gamma\in(0,1/4]$; reason: the upper bound $F\le(2+2\ln(2\gamma^2H))H$ is attained up to an absolute factor on the family $d_m$
--   - generalization: a randomized ball design (a random family of distinct eligible balls) over the indexed balls $B_{j\ell}$ (distinct distances) → a randomized ball design (a random finite set of eligible pairs, two pairs possibly giving the same ball) in the pair encoding of the published certificate workload (a pair $(j,i)$ with $d(j,i)<\gamma$ is the ball $B(j,d(j,i))$; a repeated distance duplicates a ball); reason: a design over distinct balls is the special case using one pair per ball (same coverage, same cost), so the statement specializes to the source's
--   - encoding: expected geometric cost and coverage probability → $\sum_S\mu_S(S)\sum_{(j,i)\in S}(\gamma-d(j,i))^{-2}$ in $[0,\infty]$ and $\mu_S\{S:\exists(j,i)\in S,\ d(i',j)\le d(j,i)\}$, for a probability mass function $\mu_S$; reason: same quantities for a random finite family
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem D, p.3; Proposition 4.3, p.9

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_dm
import Definitions.Def_MetricMinTest_infoWorkload
import Definitions.Def_MetricMinTest_certWorkload
import Definitions.Def_MetricMinTest_Bstar

namespace MetricMinTest.Supplement

/-- **Theorem D (The price of local thresholds).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem D, p.3: "For every finite metric
or pseudometric and γ, δ ∈ (0, 1/4], H ≤ F ≤ [2 + 2 ln(2γ²H)] H, B⋆_d(γ, δ) = O(FL). The
logarithmic conversion factor is attained on d_m. If every fixed index is covered with probability
at least p, any randomized ball design has expected geometric cost at least pF."

**Formalization Note.** `H = infoWorkload`, `F = certWorkload`, `L = ln(1/δ)`; the `O` has an
absolute constant. "Attained on d_m": an absolute `c > 0` with
`F_{d_m}(γ) ≥ c[2 + 2 ln(2γ²H_{d_m}(γ))]H_{d_m}(γ)` for every `m ≥ 1`, `γ ∈ (0, 1/4]`. The design
clause is Proposition 4.3 (p.9): for `p ∈ (0, 1]`, a randomized ball design is any law `μS` (a
`PMF`, arbitrary correlations) on finite families of eligible balls, a ball being encoded as in
the published `certWorkload` by a pair `(j, i)` with `d j i < γ` (ball `B(j, d j i)`, geometric
cost `(γ − d j i)⁻²`); index `i'` is covered if `d(i', j) ≤ d(j, i)` for some selected pair.
The expected geometric cost is `∑_S μS(S) ∑_{(j,i)∈S} (γ − d j i)⁻²` in `ℝ≥0∞`. -/
theorem theorem_D :
    ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧
      (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ), IsPseudometric d →
        ∀ γ δ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → δ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
          infoWorkload d γ ≤ certWorkload d γ ∧
          certWorkload d γ ≤ (2 + 2 * Real.log (2 * γ ^ 2 * infoWorkload d γ)) * infoWorkload d γ ∧
          Bstar d γ δ ≤ ENNReal.ofReal (C₁ * certWorkload d γ * Real.log (1 / δ))) ∧
      (∀ m : ℕ, 1 ≤ m → ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) →
        c * ((2 + 2 * Real.log (2 * γ ^ 2 * infoWorkload (dm m γ) γ)) * infoWorkload (dm m γ) γ) ≤
          certWorkload (dm m γ) γ) ∧
      (∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ), IsPseudometric d →
        ∀ γ : ℝ, γ ∈ Set.Ioc (0 : ℝ) (1 / 4) → ∀ p : ℝ, p ∈ Set.Ioc (0 : ℝ) 1 →
        ∀ μS : PMF (Finset (ι × ι)),
          (∀ S ∈ μS.support, ∀ q ∈ S, d q.1 q.2 < γ) →
          (∀ i, ENNReal.ofReal p ≤ μS.toOuterMeasure {S | ∃ q ∈ S, d i q.1 ≤ d q.1 q.2}) →
          ENNReal.ofReal (p * certWorkload d γ) ≤
            ∑' S, μS S * ENNReal.ofReal (∑ q ∈ S, ((γ - d q.1 q.2) ^ 2)⁻¹)) := by sorry

end MetricMinTest.Supplement
