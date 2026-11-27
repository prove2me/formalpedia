-- Prove2me | Theorems.Thm_HedgePSNV_Supplement_lemma_ec_12
-- name    : HedgePSNV.Supplement.lemma_ec_12
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:59:07.251955+00:00
-- url     : https://prove2.me/theorems/7f34ca44-bef4-5778-a9c7-a8db658b3f3e
-- title:
--   Lemma EC.12 — with increasing differences, the expected-payoff gap between stochastically ordered factors increases in $q$
-- statement:
--   Let $H:\mathbb R^n\times\mathbb R^J\to\mathbb R$ have increasing differences in $(q,a)$ (decisions $q\ge0$), with $H(q,\cdot)$ Borel. Let $A_1$ and $A_2$ be $\mathbb R^J$-valued random vectors on probability spaces $(\Omega_1,\mathbb P_1)$ and $(\Omega_2,\mathbb P_2)$ with $A_1\preceq A_2$ in the usual multivariate stochastic order ($\mathbb P(A_1\in U)\le\mathbb P(A_2\in U)$ for every upper set $U\subseteq\mathbb R^J$), and suppose $H(q,A_i)$ is integrable for every $q\ge0$. Then for all $0\le q_1\le q_2$,
--   $$
--   \mathbb E[H(q_1,A_2)]-\mathbb E[H(q_1,A_1)]\le\mathbb E[H(q_2,A_2)]-\mathbb E[H(q_2,A_1)],
--   $$
--   i.e. $\mathbb E[H(q,A_2)]-\mathbb E[H(q,A_1)]$ is entry-wise increasing in $q$.
--
--   It is the step of Theorem EC.3: a stochastically larger factor raises the marginal value of every decision.
--
--   Differences from the source:
--   - encoding: $A_1\preceq A_2$: $\mathbb P(A_1\in U)\le\mathbb P(A_2\in U)$ for every upper set $U\subseteq\mathbb R^J$ → the published `StochasticOrders.Multivariate.MultivariateOrder` (v2): $\mathbb E[\varphi(A_1)]\le\mathbb E[\varphi(A_2)]$ for Borel increasing $\varphi$ with finite expectations; reason: for random vectors on probability spaces this is the upper-set order with Borel upper sets (Shaked–Shanthikumar (6.B.4)); $\mathbb P(A\in U)$ presupposes $U$ measurable; the proof of Lemma EC.12 uses the function form (p.ec61)
--   - encoding: the expectations $\mathbb E[H_T(q,A_i)]$ → $H_T(q,\cdot)$ Borel and $H_T(q,A_i)$ integrable for every $q\ge0$; reason: the paper takes these expectations; otherwise the Bochner integral is a default $0$
--   - reading: “entry-wise increasing in $q$” → for all decisions $0\le q_1\le q_2$ (coordinatewise); reason: the proof: “For any $q_2\ge q_1\ge0$” (p.ec61); increasing in each entry is equivalent to the order form
--   - encoding: $A_1$ and $A_2$ random vectors compared through their laws → $A_1$ on $(\Omega_1,\mathbb P_1)$ and $A_2$ on $(\Omega_2,\mathbb P_2)$, possibly different probability spaces; reason: the order hypothesis, the expectations and the conclusion depend only on the laws of $A_1$ and $A_2$; one common space is the instance $\Omega_1=\Omega_2$
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Lemma EC.12, p.ec61 (PDF 97)

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_PayoffAssumptions
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

/-- Lemma EC.12, arXiv:2201.01026v4, p.ec61: for any given `A_1 ⪯ A_2` (defined as
`P(A_1 ∈ U) ≤ P(A_2 ∈ U)` for any upper set `U ⊆ ℝᴶ`), suppose `H_T(q,a)` has increasing
differences in `(q,a)`. Then `E[H_T(q,A_2)] − E[H_T(q,A_1)]` is entry-wise increasing in `q`.

Precisely: `A_1` and `A_2` are `ℝᴶ`-valued random vectors on probability spaces `(Ω₁, P₁)` and
`(Ω₂, P₂)` (possibly different), ordered in the usual multivariate stochastic order; for
decisions `0 ≤ q₁ ≤ q₂`, `E[H(q₁,A_2)] − E[H(q₁,A_1)] ≤ E[H(q₂,A_2)] − E[H(q₂,A_1)]`.

**Formalization Note** The order is the published
`StochasticOrders.Multivariate.MultivariateOrder` (v2: `E[φ(A_1)] ≤ E[φ(A_2)]` for every Borel
increasing `φ` with both expectations finite), which for random vectors on probability spaces is
the upper-set order of the paper with Borel upper sets (Shaked–Shanthikumar (6.B.4); the proof
uses it in this form, p.ec61). The expectations `E[H_T(q, A_i)]` are presupposed: `H(q, ·)` is
Borel and `H(q, A_i)` is integrable for every `q ≥ 0`. Decisions range over `q ≥ 0` (p.ec14). -/
theorem lemma_ec_12 {n J : ℕ} (H : (Fin n → ℝ) → (Fin J → ℝ) → ℝ)
    (hH : ∀ q : Fin n → ℝ, Measurable (H q)) (hID : HasIncreasingDifferences H)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (A₁ : Ω₁ → Fin J → ℝ) (A₂ : Ω₂ → Fin J → ℝ)
    (hint₁ : ∀ q : Fin n → ℝ, 0 ≤ q → Integrable (fun ω => H q (A₁ ω)) P₁)
    (hint₂ : ∀ q : Fin n → ℝ, 0 ≤ q → Integrable (fun ω => H q (A₂ ω)) P₂)
    (hord : StochasticOrders.Multivariate.MultivariateOrder P₁ P₂ A₁ A₂) :
    ∀ q₁ q₂ : Fin n → ℝ, 0 ≤ q₁ → q₁ ≤ q₂ →
      (∫ ω, H q₁ (A₂ ω) ∂P₂) - (∫ ω, H q₁ (A₁ ω) ∂P₁) ≤
        (∫ ω, H q₂ (A₂ ω) ∂P₂) - (∫ ω, H q₂ (A₁ ω) ∂P₁) := by sorry

end HedgePSNV.Supplement
