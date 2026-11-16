-- Prove2me | Theorems.Thm_MetricMinTest_Supplement_theorem_D_3
-- name    : MetricMinTest.Supplement.theorem_D_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:49:06.852238+00:00
-- url     : https://prove2.me/theorems/3b11501d-f13b-4798-8021-0c17274ef5b6
-- title:
--   Theorem D.3, p.27 — from a fractional ball cover of cost $C$: expected cost $100CL$, and budget $1300CL$ with expected cost $162CL$
-- statement:
--   Let $d$ be a finite metric or pseudometric, $\gamma,\delta\in(0,1/4]$ and $L=\ln(1/\delta)$. For every feasible fractional ball cover of cost $C$ there is a $(\gamma,\delta)$-valid tester with positive-instance expected cost at most $100\,C\ln(1/\delta)$. Another valid tester satisfies $\tau\le1300\,C\ln(1/\delta)$ on every realization and
--   $$\sup_{P\in\mathcal P_d^+(\gamma)}\mathbb E_P\,\tau\le162\,C\ln(1/\delta).$$
--
--   With $C=F$ this gives $B^\star_d=O(FL)$ (Theorem D).
--
--   Differences from the source:
--   - encoding: a finite metric or pseudometric on $[k]$ → a pseudometric on a finite nonempty index type ($k=|\iota|\ge1$); reason: a metric is a pseudometric; $[k]$ has $k\ge1$ points
--   - generalization: "every feasible cover of cost $C$", for covers over the indexed balls $B_{j\ell}$ (distinct distances) → "every feasible cover of cost $C$", for covers in the pair encoding of the published certificate workload (a pair $(j,i)$ with $d(j,i)<\gamma$ is the ball $B(j,d(j,i))$; a repeated distance duplicates a ball); reason: a cover over distinct balls is the special case supported on one pair per ball, so the statement specializes to the source's
--   - encoding: "on every realization" → for every private draw and every observation table; reason: same quantifier
--   - encoding: the cost measures and testers of §2 (sequential testers with private randomness; $C^\star$, $B^\star$, $C^{\mathrm{na}}$, $B^{\mathrm{na}}$) → the published tester model (stack-of-streams observations, validity including measurability of the acceptance event and the stopping time) and $[0,\infty]$-valued infima, suprema and expectations; reason: same quantities; probabilities and expectations require measurability, and the values can be infinite
-- source:
--   Chen–Fang, Minimum-Mean Testing under Metric Constraints: Shared Information, Certificates, and Adaptivity, STOC 2027 submission (manuscript sha256 dcece1939edb1fcf752ab6152794f04d8762928ada557c99626997db01ad32bb), Theorem D.3, p.27

import Mathlib
import Definitions.Def_MetricMinTest_IsPseudometric
import Definitions.Def_MetricMinTest_Tester_IsValid
import Definitions.Def_MetricMinTest_Supplement_IsBallCover
import Definitions.Def_MetricMinTest_Supplement_ballCoverCost

namespace MetricMinTest.Supplement

open MeasureTheory

/-- **Theorem D.3 (Finite-confidence expectation and deterministic budget).** Chen–Fang, *Minimum-Mean Testing under Metric Constraints*, STOC 2027 submission (manuscript sha256 dcece193…ad32bb), Theorem D.3,
p.27: "For every feasible cover of cost C there is a valid tester with positive-instance expected
cost at most 100 C ln(1/δ). Another valid tester satisfies τ ≤ 1300 C ln(1/δ) on every realization
and sup_{P∈P_d^+(γ)} E_P τ ≤ 162 C ln(1/δ)."

**Formalization Note.** Standing setting (§2): `d` a pseudometric on a finite nonempty index type,
`γ, δ ∈ (0, 1/4]`. A feasible cover is a fractional ball cover (`IsBallCover`), `C` its cost
`ballCoverCost`. "Valid" is the published `Tester.IsValid`; "every realization" is every private
draw `ξ` and every observation table `ω`. -/
theorem theorem_D_3 {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] (d : ι → ι → ℝ)
    (hd : IsPseudometric d) (γ δ : ℝ) (hγ : γ ∈ Set.Ioc (0 : ℝ) (1 / 4))
    (hδ : δ ∈ Set.Ioc (0 : ℝ) (1 / 4)) (y : ι × ι → ℝ) (hy : IsBallCover d γ y) :
    (∃ T : Tester ι, T.IsValid d γ δ ∧
      (⨆ (P : Instance ι) (_ : IsPositive d γ P),
        ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))) ≤
        ENNReal.ofReal (100 * ballCoverCost d γ y * Real.log (1 / δ))) ∧
    (∃ T : Tester ι, T.IsValid d γ δ ∧
      (∀ ξ ω, ((T.stopTime ξ ω : ℕ∞) : ENNReal) ≤
        ENNReal.ofReal (1300 * ballCoverCost d γ y * Real.log (1 / δ))) ∧
      (⨆ (P : Instance ι) (_ : IsPositive d γ P),
        ∫⁻ p, ((T.stopTime p.1 p.2 : ℕ∞) : ENNReal) ∂(T.μξ.prod (streamLaw P))) ≤
        ENNReal.ofReal (162 * ballCoverCost d γ y * Real.log (1 / δ))) := by sorry

end MetricMinTest.Supplement
