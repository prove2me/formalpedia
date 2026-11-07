-- Prove2me | Theorems.Thm_HedgePSNV_proposition_1
-- name    : HedgePSNV.proposition_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T12:01:30.857377+00:00
-- url     : https://prove2.me/theorems/f931358d-1168-43a8-8961-581c9875577e
-- title:
--   Proposition 1 — the newsvendor problem (2) has a unique solution, characterized by (4)
-- statement:
--   Let $\nu$ be the law of the market size, with distribution function $F$, and suppose Assumption 1 holds for $\nu$. Let $(P^{NV},R^{NV})$ maximize the expected production payoff $\mathbb E[H_T(P,R)]=(P-c)(R-bP)-(P-s)\mathbb E[(R-A)^+]$ over the decision domain $D=\{P\ge c,\ R-bP\ge0\}$, and suppose Assumption 2 holds there: $P^{NV}>c$, $R^{NV}-bP^{NV}>0$ and $\mathbb E[H_T(P^{NV},R^{NV})]>0$. Then
--
--   1. $(P^{NV},R^{NV})$ is the only maximizer of problem (2);
--   2. it satisfies the optimality equations (4):
--   $$
--   2bP^{NV}-bc=\mathbb E\big(R^{NV}\wedge A\big),\qquad F\big(R^{NV}\big)=\frac{P^{NV}-c}{P^{NV}-s}.
--   $$
--
--   This is the benchmark solution against which the hedging decisions of Theorem 2 are compared.
--
--   **Formalization Note** The second equation is the paper's $R^{NV}=F^{-1}\big((P^{NV}-c)/(P^{NV}-s)\big)$; under Assumption 1 $F$ is continuous and strictly increasing where it lies in $(0,1)$, and the ratio lies in $(0,1)$, so the two forms are equivalent. No integrability hypothesis is needed: $\mathbb E[H_T(P^{NV},R^{NV})]>0$ forces it.
--
--   Differences from the source:
--   - generalization: the market size $A_T=C_T+\tilde\sigma\tilde B_T$ of the model → any law $\nu$ on $\mathbb R$ satisfying Assumption 1; reason: problem (2) depends on $A_T$ only through its law, so the paper's statement is the case $\nu=$ law of $A_T$
--   - reading: "has a unique solution", with Assumption 2 stated at that solution → a maximizer at which Assumption 2's inequalities hold is the only maximizer; reason: Assumption 2 refers to "the" solution, so its existence is part of the hypothesis
--   - reading: arg max / arg min over $(P,R)$ → over the decision domain $D=\{P\ge c,\ R-bP\ge0\}$ of (2); reason: p.9: the constraints are non-binding and "the same applies to all relevant settings throughout the paper"
--   - encoding: $R^{NV}=F^{-1}\big(\frac{P^{NV}-c}{P^{NV}-s}\big)$ → $F(R^{NV})=\frac{P^{NV}-c}{P^{NV}-s}$; reason: equivalent: under Assumption 1 $F$ is continuous and strictly increasing on $F^{-1}((0,1))$, and the ratio lies in $(0,1)$
--   - reading: $c$ the unit production cost and $s$ the unit salvage value → $s<c$ in the parameter structure; reason: the newsvendor convention (p.7); the quantile level in (4) needs it
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Proposition 1 and (4), p.8

import Mathlib
import Definitions.Def_HedgePSNV_Newsvendor

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

/-- Proposition 1, arXiv:2201.01026v4, p.8: under Assumptions 1 and 2, the
profit-maximization problem (2) has a unique solution, characterized by the optimality
equations (4): `2bP^NV − bc = E(R^NV ∧ A_T)` and `R^NV = F^{−1}((P^NV − c)/(P^NV − s))`.

Stated for a market-size law `ν` on `ℝ` (problem (2) depends on `A_T` only through its law).
Assumption 2 refers to "the" solution: it is the hypothesis that `(PNV, RNV)` is a maximizer
with the three inequalities. The conclusion is that it is the only maximizer over the decision
domain and that (4) holds, the quantile equation written as `F(R^NV) = (P^NV − c)/(P^NV − s)`.

**Formalization Note** `F = cdf ν` is continuous and strictly increasing under Assumption 1,
so `R = F^{−1}(q)` and `F(R) = q` are equivalent for `q ∈ (0, 1)`. No integrability
hypothesis is needed: `E[H_T(P^NV,R^NV)] > 0` in Assumption 2 already forces the payoff, hence
the negative part of the market size, to be integrable (a non-integrable Bochner integral is
`0`). -/
theorem proposition_1 (p : Params) (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (h1 : Assumption1 ν)
    (PNV RNV : ℝ) (hNV : IsNVMaximizer p ν id PNV RNV) (h2 : Assumption2 p ν id PNV RNV) :
    (∀ P R : ℝ, IsNVMaximizer p ν id P R → P = PNV ∧ R = RNV) ∧
    2 * p.b * PNV - p.b * p.c = ∫ a, min RNV a ∂ν ∧
    cdf ν RNV = (PNV - p.c) / (PNV - p.s) := by sorry

end HedgePSNV
