-- Prove2me | Theorems.Thm_HedgePSNV_Supplement_theorem_ec_3
-- name    : HedgePSNV.Supplement.theorem_ec_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T03:59:38.876637+00:00
-- url     : https://prove2.me/theorems/0ee77398-5f10-445c-bf47-05309a0b2a18
-- title:
--   Theorem EC.3 (Extension of Topkis) — the smallest maximizer of $\mathbb E[H_T(q,A)]$ increases with $A$ in the multivariate stochastic order
-- statement:
--   Let $H:\mathbb R^n\times\mathbb R^J\to\mathbb R$ satisfy Assumption EC.1 (concave in each $q_i$, increasing in $a$, supermodular in $q$, increasing differences in $(q,a)$, on decisions $q\ge0$), with $H(q,\cdot)$ Borel. Let $A_1,A_2$ be $\mathbb R^J$-valued random vectors on probability spaces $(\Omega_1,\mathbb P_1)$, $(\Omega_2,\mathbb P_2)$ with $H(q,A_i)$ integrable for $q\ge0$, and let
--   $$
--   q^*_i=\min\arg\max_{q\ge0}\mathbb E[H(q,A_i)],\qquad i=1,2,
--   $$
--   be the least maximizers. If $A_1\preceq A_2$ in the usual multivariate stochastic order, then
--   $$
--   q^*_1\le q^*_2 .
--   $$
--
--   In the proof of Theorem EC.1 it gives $q^{*M}\le q^*$ under positive impact.
--
--   **Formalization Note** No differentiability is assumed (the printed proof differentiates $\mathbb E[H(q,A)]$).
--
--   Differences from the source:
--   - reading: Assumption EC.1 (i)–(iv) with decisions “without loss of generality … $q\ge0$” (p.ec14) → all four parts on the orthant $q\ge0$; concavity in each $q_i\ge0$ with the other coordinates fixed; supermodularity with coordinatewise $\vee,\wedge$; reason: decisions are restricted to $q\ge0$ throughout §EC.5
--   - reading: $q^*:=\min\{\arg\max_{q\ge0}\cdot\}$, “there exists a smallest optimal solution … (Topkis 1978)” (p.ec16) → the least maximizer is a hypothesis (`IsLeast (orthantArgmax …)`), not constructed; reason: the existence argument needs compactness the setting lacks; the theorem is about the least maximizer whenever it exists
--   - encoding: $A_1\preceq A_2$: $\mathbb P(A_1\in U)\le\mathbb P(A_2\in U)$ for every upper set $U\subseteq\mathbb R^J$ → the published `StochasticOrders.Multivariate.MultivariateOrder` (v2): $\mathbb E[\varphi(A_1)]\le\mathbb E[\varphi(A_2)]$ for Borel increasing $\varphi$ with finite expectations; reason: for random vectors on probability spaces this is the upper-set order with Borel upper sets (Shaked–Shanthikumar (6.B.4)); $\mathbb P(A\in U)$ presupposes $U$ measurable; the proof of Lemma EC.12 uses the function form (p.ec61)
--   - encoding: the expectations $\mathbb E[H_T(q,A_i)]$ → $H_T(q,\cdot)$ Borel and $H_T(q,A_i)$ integrable for every $q\ge0$; reason: the paper takes these expectations; otherwise the Bochner integral is a default $0$
--   - encoding: $A_1$ and $A_2$ random vectors compared through their laws → $A_1$ on $(\Omega_1,\mathbb P_1)$ and $A_2$ on $(\Omega_2,\mathbb P_2)$, possibly different probability spaces; reason: the order hypothesis, the expectations and the conclusion depend only on the laws of $A_1$ and $A_2$; one common space is the instance $\Omega_1=\Omega_2$
-- source:
--   Wang–Yao–Zhang, How Does Risk Hedging Impact Operations? Insights from a Price-Setting Newsvendor Model, arXiv:2201.01026v4, Theorem EC.3, p.ec62 (PDF 98)

import Mathlib
import Definitions.Def_HedgePSNV_Supplement_PayoffAssumptions
import Definitions.Def_StochasticOrders_Multivariate_MultivariateOrder_v2

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace HedgePSNV.Supplement

/-- Theorem EC.3 (Extension of Topkis Theorem), arXiv:2201.01026v4, p.ec62: suppose `H_T(q,a)`
satisfies Assumption EC.1. Let `q*_i = min arg max_{q ≥ 0} E[H_T(q, A_i)]`, `i = 1, 2`. If
`A_1 ⪯ A_2`, then `q*_1 ≤ q*_2`.

Precisely: `A_1`, `A_2` are `ℝᴶ`-valued random vectors on probability spaces `(Ω₁, P₁)`,
`(Ω₂, P₂)` (possibly different) ordered in the usual multivariate stochastic order, and `q*_i`
is the least element (coordinatewise) of the set of maximizers of `q ↦ E[H_T(q, A_i)]` over
`q ≥ 0`; then `q*_1 ≤ q*_2` coordinatewise.

**Formalization Note** The least maximizers are hypotheses (`IsLeast`), not constructed: the
paper's existence argument (supermodularity and Topkis 1978, p.ec16) needs a compactness the
setting does not provide. The order is the published `MultivariateOrder` (v2), the paper's
upper-set order for random vectors on probability spaces (see Lemma EC.12). The expectations
are presupposed: `H(q, ·)` is Borel and `H(q, A_i)` integrable for `q ≥ 0`. The printed proof
differentiates `E[H_T(q, A)]`; no differentiability is assumed. -/
theorem theorem_ec_3 {n J : ℕ} (H : (Fin n → ℝ) → (Fin J → ℝ) → ℝ)
    (hH : ∀ q : Fin n → ℝ, Measurable (H q)) (hEC1 : AssumptionEC1 H)
    {Ω₁ Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (P₁ : Measure Ω₁) (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    (A₁ : Ω₁ → Fin J → ℝ) (A₂ : Ω₂ → Fin J → ℝ)
    (hint₁ : ∀ q : Fin n → ℝ, 0 ≤ q → Integrable (fun ω => H q (A₁ ω)) P₁)
    (hint₂ : ∀ q : Fin n → ℝ, 0 ≤ q → Integrable (fun ω => H q (A₂ ω)) P₂)
    (q₁ q₂ : Fin n → ℝ)
    (hq₁ : IsLeast (orthantArgmax fun q => ∫ ω, H q (A₁ ω) ∂P₁) q₁)
    (hq₂ : IsLeast (orthantArgmax fun q => ∫ ω, H q (A₂ ω) ∂P₂) q₂)
    (hord : StochasticOrders.Multivariate.MultivariateOrder P₁ P₂ A₁ A₂) :
    q₁ ≤ q₂ := by sorry

end HedgePSNV.Supplement
