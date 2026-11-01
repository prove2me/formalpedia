-- Prove2me | Theorems.Thm_HedgePSNV_lemma_ec_6
-- name    : HedgePSNV.lemma_ec_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T12:01:46.742876+00:00
-- url     : https://prove2.me/theorems/dca78545-d3d9-4bbe-89b3-86cefb2377a3
-- title:
--   Lemma EC.6 — a stochastically larger market raises the newsvendor price and VPQ, and the expected payoff
-- statement:
--   Let $\nu_1\preceq\nu_2$ be two market-size laws on $\mathbb R$ in the usual stochastic order ($\nu_1(x,\infty)\le\nu_2(x,\infty)$ for all $x$), both satisfying Assumption 1, with $\mathbb E_{\nu_1}[A^-]<\infty$. Let $(P^{NV}_2,R^{NV}_2)$ be the solution of problem (2) under $\nu_2$, i.e. its unique maximizer over $D$. Then
--
--   1. every maximizer $(P^{NV}_1,R^{NV}_1)$ of problem (2) under $\nu_1$ satisfies
--   $$
--   P^{NV}_1\le P^{NV}_2,\qquad R^{NV}_1\le R^{NV}_2;
--   $$
--   2. $\mathbb E_{\nu_1}[H_T(P,R)]\le\mathbb E_{\nu_2}[H_T(P,R)]$ for every $(P,R)$ with $P\ge s$, in particular on $D$.
--
--   Proposition 4 is this lemma with $\nu_1$ the law of $A_T$ under $\mathbb P^M$ and $\nu_2$ its law under $\mathbb P$.
--
--   Differences from the source:
--   - generalization: $C^{(1)}_T\preceq C^{(2)}_T$ (orders the asset-driven demand components) → the market-size laws are ordered, $\nu_1\preceq\nu_2$, each satisfying Assumption 1; reason: the proof uses only $A^{(1)}_T\preceq A^{(2)}_T$, which $C^{(1)}_T\preceq C^{(2)}_T$ implies by Remark 1
--   - reading: $(P^{NV}_i,R^{NV}_i)$ "the corresponding solutions to problem (2)" → uniqueness is a hypothesis for $\nu_2$; the conclusion holds for every maximizer under $\nu_1$; reason: stronger than presupposing a unique solution in both worlds; in Proposition 4 world (1) is $\mathbb P^M$, where Assumption 2 is not assumed
--   - reading: $\mathbb E[H^{(1)}_T(P,R)]\le\mathbb E[H^{(2)}_T(P,R)]$ for all $(P,R)$ → for all $(P,R)$ with $P\ge s$, a superset of $D$; reason: for $P<s$ the term $-(P-s)(R-A)^+$ decreases in $A$, so the inequality reverses; the paper's pairs lie in $D$, where $P\ge c>s$
--   - encoding: the expectations $\mathbb E[H^{(i)}_T]$ (finite, presupposed) → $\mathbb E_{\nu_1}[A^-]<\infty$; for $\nu_2$ it follows from uniqueness; reason: otherwise the Bochner integral is $0$ and every point of $D$ maximizes
--   - reading: arg max / arg min over $(P,R)$ → over the decision domain $D=\{P\ge c,\ R-bP\ge0\}$ of (2); reason: p.9: the constraints are non-binding and "the same applies to all relevant settings throughout the paper"
--   - reading: $c$ the unit production cost and $s$ the unit salvage value → $s<c$ in the parameter structure; reason: the newsvendor convention (p.7)
--   - generalization: Assumptions 1–3, imposed "throughout the paper" (p.8) → Assumption 1 for both laws, Assumptions 2–3 for neither, uniqueness of the maximizer only under $\nu_2$; reason: the expected payoff is supermodular in $(P,R)$ on the sublattice $D$ with increasing differences in the law, so a unique maximizer under $\nu_2$ dominates every maximizer under $\nu_1$; with $\nu_2$ the law of $A_T$ under $\mathbb P$, Assumptions 1–2 give that uniqueness (Proposition 1), which specializes to the paper's use in Proposition 4
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Lemma EC.6, p.ec47 (PDF 83); proof pp.ec47–ec48

import Mathlib
import Definitions.Def_HedgePSNV_Newsvendor
import Definitions.Def_StochasticOrders_Usual_UsualOrder

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV

/-- Lemma EC.6, arXiv:2201.01026v4, p.ec47: as the market size increases
stochastically, the newsvendor's optimal price and virtual production quantity increase, and
so does the expected production payoff.

For two market-size laws `ν₁ ⪯ ν₂` (usual stochastic order), each satisfying Assumption 1,
where `(P₂, R₂)` is the solution of problem (2) under `ν₂` (its unique maximizer over the
decision domain): every maximizer `(P₁, R₁)` of problem (2) under `ν₁` satisfies `P₁ ≤ P₂`
and `R₁ ≤ R₂`; and `E[H^(1)_T(P,R)] ≤ E[H^(2)_T(P,R)]` for every `(P, R)` with `P ≥ s`
(in particular on the decision domain, where `P ≥ c > s`).

**Formalization Note** The paper orders `C^(1)_T ⪯ C^(2)_T`; its proof uses only the induced
order `A^(1)_T ⪯ A^(2)_T` of the market sizes (Remark 1), which is the hypothesis here, on the
laws. "The solution" of problem (2) is encoded for the larger law as a maximizer that is the
only one; for the smaller law the claim is made for every maximizer. For `P < s` the
expected payoff is decreasing in the market size, so the comparison is stated for `P ≥ s`. The
integrability of the negative part of the smaller market size states that the expectations
`E[H^(1)_T(P,R)]` exist (otherwise every point of the domain maximizes the junk value `0`);
for the larger law it follows from the uniqueness hypothesis. -/
theorem lemma_ec_6 (p : Params) (ν₁ ν₂ : Measure ℝ) [IsProbabilityMeasure ν₁]
    [IsProbabilityMeasure ν₂]
    (hint₁ : Integrable (fun a => max (-a) 0) ν₁)
    (h1₁ : Assumption1 ν₁) (h1₂ : Assumption1 ν₂)
    (hord : StochasticOrders.Usual.UsualOrder ν₁ ν₂ id id)
    (P₂ R₂ : ℝ) (hNV₂ : IsNVMaximizer p ν₂ id P₂ R₂)
    (huniq₂ : ∀ P R : ℝ, IsNVMaximizer p ν₂ id P R → P = P₂ ∧ R = R₂) :
    (∀ P₁ R₁ : ℝ, IsNVMaximizer p ν₁ id P₁ R₁ → P₁ ≤ P₂ ∧ R₁ ≤ R₂) ∧
    ∀ P R : ℝ, p.s ≤ P → nvValue p ν₁ id P R ≤ nvValue p ν₂ id P R := by sorry

end HedgePSNV
