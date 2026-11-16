-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_D_2
-- name    : MetricMinTest.Supplement.theorem_D_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:48:20.409205+00:00
-- url     : https://prove2.me/theorems/7b47b3f7-c169-4fc5-bfaa-54b5c22760b2
-- title:
--   Theorem D.2, p.26 — RandBall$_u(y)$: errors $\le2e^{-u}$, $\mathbb E\tau\le2u(u+\gamma)C(y)$, always stops
-- statement:
--   Let $d$ be a finite metric or pseudometric and $\gamma\in(0,1/4]$. For every fractional ball cover $y$ and every $u>0$, each error probability of RandBall$_u(y)$ is at most $2e^{-u}$: it accepts a violating instance of $\mathcal P_d$ with probability at most $2e^{-u}$, and rejects a positive instance with probability at most $2e^{-u}$. On every positive instance,
--   $$\mathbb E\,\tau\le2u(u+\gamma)\,C(y).$$
--   The procedure stops after finitely many queries on every instance.
--
--   Random selection of certificates with probabilities proportional to a fractional cover therefore pays the fractional cover cost, not an integral one.
--
--   **Formalization Note** The statement holds for every fixed order of the selected balls.
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - generalization: "every fractional cover $y$", for covers over the indexed balls $B_{j\ell}$ (distinct distances) → "every fractional cover $y$", for covers in the pair encoding of the published certificate workload (a pair $(j,i)$ with $d(j,i)<\gamma$ is the ball $B(j,d(j,i))$; a repeated distance duplicates a ball); reason: a cover over distinct balls is the special case supported on one pair per ball, so the statement specializes to the source's
--   - encoding: RandBall$_u(y)$ "in a fixed order" → the procedure for every duplicate-free enumeration of the pairs; reason: the procedure is defined up to the order and the claim is for each
--   - reading: each error probability → $\Pr(\text{accept})$ on every violating $P\in\mathcal P_d$ and $\Pr(\text{reject})$ on every positive instance; reason: the two errors of the testing contract (Definition 2.1)
--   - reading: stops after finitely many queries on every instance → finite stopping time for every private draw and every observation table; reason: the strongest reading
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem D.2, p.26

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_Supplement_randBall
import Definitions.Def_MetricMinTest_Supplement_IsBallCover
import Definitions.Def_MetricMinTest_Supplement_ballCoverCost

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem D.2 (Random selection and sequential certification).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem D.2, p.26: "For
every fractional cover y and u > 0, each error probability of RandBall_u(y) is at most 2e^{−u}. On
every positive instance, Eτ ≤ 2u(u + γ)C(y). The procedure stops after finitely many queries on
every instance."

**Formalization Note.** Standing setting (§2): `d` a pseudometric on a finite nonempty index type,
`γ ∈ (0, 1/4]`. `y` is any fractional ball cover (`IsBallCover`, the indexed-ball encoding of the
published `certWorkload`) and `C(y) = ballCoverCost d γ y`. `RandBall_u(y)` is
`randBall d γ u y ord` for every fixed order `ord` (a duplicate-free enumeration of the pairs).
The two error probabilities are `Pr_P(accept)` on every violating `P ∈ P_d` and `Pr_P(reject)` on
every positive instance, over `μξ ⊗ streamLaw P`. "Stops after finitely many queries on every
instance" is a finite stopping time for every private draw and every observation table. -/
theorem theorem_D_2 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (y : ι × ι → ℝ)
    (hy : IsBallCover d γ y) (u : ℝ) (hu : 0 < u) (ord : List (ι × ι)) (hnodup : ord.Nodup)
    (hall : ∀ p, p ∈ ord) :
    (∀ P : Instance ι, InClass d P → IsViolating P →
      ((randBall d γ u y ord).μξ.prod (streamLaw P))
          {p | (randBall d γ u y ord).Accepts p.1 p.2} ≤
        ENNReal.ofReal (2 * Real.exp (-u))) ∧
    (∀ P : Instance ι, IsPositive d γ P →
      ((randBall d γ u y ord).μξ.prod (streamLaw P))
          {p | ¬ (randBall d γ u y ord).Accepts p.1 p.2} ≤
        ENNReal.ofReal (2 * Real.exp (-u))) ∧
    (∀ P : Instance ι, IsPositive d γ P →
      ∫⁻ p, (((randBall d γ u y ord).stopTime p.1 p.2 : ℕ∞) : ENNReal)
          ∂((randBall d γ u y ord).μξ.prod (streamLaw P)) ≤
        ENNReal.ofReal (2 * u * (u + γ) * ballCoverCost d γ y)) ∧
    (∀ ξ ω, (randBall d γ u y ord).stopTime ξ ω ≠ ⊤) := by sorry

end MetricMinTest.Supplement
