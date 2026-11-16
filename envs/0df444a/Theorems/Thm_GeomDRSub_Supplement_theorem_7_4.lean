-- Prove2me | Theorems.Thm_GeomDRSub_Supplement_theorem_7_4
-- name    : GeomDRSub.Supplement.theorem_7_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-15T18:53:20.107972+00:00
-- url     : https://prove2.me/theorems/c66f42a8-c60a-4338-9d0c-a816f49a2212
-- title:
--   Theorem 7.4 — online and offline approximation intervals $\underline\alpha(\zeta)\le\alpha_{\mathrm{on}}(\zeta)\le\alpha_{\mathrm{oracle}}(\zeta)\le\bar\alpha(\zeta)$
-- statement:
--   For a diagonal level $\zeta\in[0,1]$, let $\alpha_{\mathrm{oracle}}(\zeta)$ be the offline oracle coefficient of Definition 6.1. It is the best expected approximation coefficient for maximizing a nonnegative $C^1$ DR-submodular function over a down-closed $K\ni\zeta\mathbf 1$ with polynomially many exact value–gradient queries and exact projections. Let $\alpha_{\mathrm{on}}(\zeta)$ be the online coefficient of Section 7.2: the best coefficient $a$ for which a uniform online algorithm has polynomially many calls and $a$-regret at most a polynomial times $T^\kappa$ with $\kappa<1$. Let
--
--   1. $\underline\alpha(\zeta)=4c_\zeta/(2c_\zeta+1)^2$ with $c_\zeta=\max\{1/2,1-\zeta\}$ be the lower profile (11);
--   2. $\bar\alpha(\zeta)=\min\{U(\zeta),C(\zeta)\}$ be the upper profile (186);
--   3. $\beta^*=4\tau/(1+6\tau+\tau^2)\approx0.470439$ be the constant of (166).
--
--   Then the following hold.
--
--   1. For every $\zeta\in[0,1]$,
--   $$\underline\alpha(\zeta)\le\alpha_{\mathrm{on}}(\zeta)\le\alpha_{\mathrm{oracle}}(\zeta)\le\bar\alpha(\zeta).\tag{220}$$
--   2. At $\zeta=0$,
--   $$\tfrac49\le\alpha_{\mathrm{on}}(0)\le\alpha_{\mathrm{oracle}}(0)\le\beta^*.\tag{221}$$
--   3. For $\zeta\in[1/2,1]$, $\alpha_{\mathrm{on}}(\zeta)=\alpha_{\mathrm{oracle}}(\zeta)=\tfrac12$ (222).
--   4. For $1/4\le\zeta<1/2$ and $\Delta=1/2-\zeta$, both $a_\star=\alpha_{\mathrm{on}}(\zeta)$ and $a_\star=\alpha_{\mathrm{oracle}}(\zeta)$ satisfy
--   $$\frac{2\Delta^2}{(1+2\sqrt\zeta)^4}\le\frac12-a_\star\le\frac{\Delta^2}{2(1+\Delta)^2}.\tag{223}$$
--   5. In particular, for both choices, $\tfrac12-a_\star(\tfrac12-\Delta)=\Theta(\Delta^2)$ as $\Delta\downarrow0$.
--
--   The theorem places both the online and the offline coefficients of the full nonnegative $C^1$ DR-submodular class in one explicit interval for every diagonal level. The interval closes at $\zeta\ge1/2$, and its width near $\zeta=1/2$ is of order $\Delta^2$.
--
--   **Formalization Note** The two coefficients are suprema over $a\in[0,1]$ of explicitly modelled achievability conditions (`OfflineAchievable`, `OnlineAchievable`). In these conditions, oracle algorithms are measurable adaptive strategies that see the instance only through exact oracles, and only oracle calls are counted.
--
--   Differences from the source:
--   - reading: one randomized algorithm (no computation model fixed) → a measurable adaptive strategy over a seed space: each call is a function of the inputs, the seed and the previous responses; only oracle calls are counted; reason: the paper counts oracle calls only ((129), (213)) and the algorithm sees f and K only through the oracles
--   - reading: the online learner earns f_t(p_t) → the learner observes only the responses to its calls (it may query p_t, which is counted); reason: Proposition 7.3's proof (p.53) covers reward observation with at most T extra queries, so the coefficient is the same
--   - encoding: Q(T) = total number of objective queries and projections → calls made before the commit of the last action p_T are bounded; reason: later calls cannot influence any action; a learner may stop there, so the set of attained coefficients is unchanged
--   - encoding: objective queries on a round occur after the action is committed → a query made before the first commit gets an uninformative response; reason: such a query reveals nothing about any objective; same algorithms up to wasted calls
--   - encoding: OPT = max_K f; Reg uses max over o ∈ K → sSup (f '' K); the regret bound for every o ∈ K; reason: K compact and f continuous, so the maximum is attained; same values
--   - encoding: the deficit is Θ(Δ²) as Δ ↓ 0 → 1/2 − a⋆(1/2 − Δ) =Θ[𝓝[>] 0] Δ² for both a⋆ = αon and a⋆ = αoracle; reason: Mathlib's Asymptotics.IsTheta along Δ → 0⁺ is the literal reading
--   - encoding: rounds t = 1..T, dimensions d ≥ 1, fixed polynomials → 0-based rounds, every d including d = 0, MvPolynomial over ℝ; reason: d = 0 instances are trivially satisfied for every a ∈ [0,1], so the coefficients are unchanged
-- source:
--   Aggarwal–Lu, Geometry-Dependent Online and Offline Approximation for Non-Monotone DR-Submodular Maximization, arXiv:2610.00545, Theorem 7.4, p.54, (220)–(223) (definitions: Definition 6.1, p.33; Section 7.2, p.52, (213); (145)–(151), pp.37–38; (165)–(166), p.41; (180), p.45; (186), p.46)

import Mathlib
import Definitions.Def_GeomDRSub_alphaLow
import Definitions.Def_GeomDRSub_Supplement_alphaOracle
import Definitions.Def_GeomDRSub_Supplement_alphaOn
import Definitions.Def_GeomDRSub_Supplement_alphaUp
import Definitions.Def_GeomDRSub_Supplement_betaStar

namespace GeomDRSub.Supplement

open Filter Topology Asymptotics

/-- **Theorem 7.4 (online and offline approximation intervals).** Aggarwal–Lu, *Geometry-Dependent Online and Offline Approximation for Non-Monotone
DR-Submodular Maximization*, arXiv:2610.00545, Section 7.3, p.54:
"For every `ζ ∈ [0, 1]`, `α̲(ζ) ≤ αon(ζ) ≤ αoracle(ζ) ≤ ᾱ(ζ)`. (220) At zero diagonal level
`ζ = 0`, `4/9 ≤ αon(0) ≤ αoracle(0) ≤ β∗`. (221) For `ζ ≥ 1/2`, `αon(ζ) = αoracle(ζ) = 1/2`. (222)
If `1/4 ≤ ζ < 1/2`, let `∆ = 1/2 − ζ`. For either `a⋆(ζ) = αon(ζ)` or `a⋆(ζ) = αoracle(ζ)`,
`2∆²/(1 + 2√ζ)⁴ ≤ 1/2 − a⋆(ζ) ≤ ∆²/(2(1 + ∆)²)`. (223) In particular, the deficit is `Θ(∆²)` as
`∆ ↓ 0`."

Conjuncts: (220) for every `ζ ∈ [0,1]`, with `α̲ = alphaLow` (11) and `ᾱ = alphaUp` (186); (221);
(222) for `ζ ∈ [1/2, 1]`; (223) for `ζ ∈ [1/4, 1/2)` and both `a⋆`; and the `Θ(∆²)` clause, as
`1/2 − a⋆(1/2 − ∆) = Θ(∆²)` along `∆ → 0⁺` for both `a⋆`.

**Formalization Note.** `αoracle` (Definition 6.1) and `αon` ((213)) are defined in
`OfflineAchievable`/`alphaOracle` and `OnlineAchievable`/`alphaOn`: oracle algorithms see the
instance only through exact value-and-gradient queries and exact projections, and only those calls
are counted. -/
theorem theorem_7_4 :
    (∀ ζ ∈ Set.Icc (0 : ℝ) 1,
      alphaLow ζ ≤ alphaOn ζ ∧ alphaOn ζ ≤ alphaOracle ζ ∧ alphaOracle ζ ≤ alphaUp ζ) ∧
    (4 / 9 ≤ alphaOn 0 ∧ alphaOn 0 ≤ alphaOracle 0 ∧ alphaOracle 0 ≤ betaStar) ∧
    (∀ ζ ∈ Set.Icc (1 / 2 : ℝ) 1, alphaOn ζ = 1 / 2 ∧ alphaOracle ζ = 1 / 2) ∧
    (∀ ζ ∈ Set.Ico (1 / 4 : ℝ) (1 / 2), ∀ aStar ∈ ({alphaOn ζ, alphaOracle ζ} : Set ℝ),
      2 * (1 / 2 - ζ) ^ 2 / (1 + 2 * Real.sqrt ζ) ^ 4 ≤ 1 / 2 - aStar ∧
        1 / 2 - aStar ≤ (1 / 2 - ζ) ^ 2 / (2 * (1 + (1 / 2 - ζ)) ^ 2)) ∧
    ((fun Δ : ℝ => 1 / 2 - alphaOn (1 / 2 - Δ)) =Θ[𝓝[>] 0] (fun Δ : ℝ => Δ ^ 2) ∧
      (fun Δ : ℝ => 1 / 2 - alphaOracle (1 / 2 - Δ)) =Θ[𝓝[>] 0] (fun Δ : ℝ => Δ ^ 2)) := by sorry

end GeomDRSub.Supplement
