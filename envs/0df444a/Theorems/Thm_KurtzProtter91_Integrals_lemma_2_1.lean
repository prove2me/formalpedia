-- Prove2me | Theorems.Thm_KurtzProtter91_Integrals_lemma_2_1
-- name    : KurtzProtter91.Integrals.lemma_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T13:06:23.428347+00:00
-- url     : https://prove2.me/theorems/36cde8a1-88ec-48a7-bbfb-def7ac89599b
-- title:
--   Lemma 2.1 — time-change-equivariant maps continuous for local uniform convergence are Skorohod-continuous
-- statement:
--   Let $E_1$ and $E_2$ be metric spaces and let $F:D_{E_1}[0,\infty)\to D_{E_2}[0,\infty)$ satisfy $F(x\circ\lambda)=F(x)\circ\lambda$ for all $x\in D_{E_1}[0,\infty)$ and all $\lambda\in\Lambda$.
--
--   1. Suppose that whenever cadlag $x_n\to x$ uniformly on bounded intervals, $F(x_n)\to F(x)$ in the Skorohod topology. Then $x_n\to x$ in the Skorohod topology implies $F(x_n)\to F(x)$ in the Skorohod topology.
--   2. Suppose that whenever cadlag $x_n\to x$ uniformly on bounded intervals, $F(x_n)\to F(x)$ uniformly on bounded intervals. Then $x_n\to x$ in the Skorohod topology implies
--   $$(x_n,F(x_n))\to(x,F(x))\quad\text{in the Skorohod topology on }D_{E_1\times E_2}[0,\infty).$$
--
--   The lemma turns local-uniform continuity of a time-change-equivariant functional into Skorohod continuity; the paper applies it to $J_\delta$ and to the step approximation.
--
--   **Formalization Note** $F$ is a map on all paths that sends cadlag paths to cadlag paths; the equivariance and both continuity hypotheses are required only for cadlag paths. "Uniformly on bounded intervals" is uniform convergence on $[0,T]$ for every $T$.
-- source:
--   Kurtz and Protter, Weak Limit Theorems for Stochastic Integrals and Stochastic Differential Equations, Ann. Probab. 19 (1991), p. 1038, Lemma 2.1

import Mathlib
import Definitions.Def_KurtzProtter91_Integrals_Skorohod

open Filter Topology
open scoped NNReal ENNReal

namespace KurtzProtter91.Integrals

theorem lemma_2_1 {E₁ E₂ : Type*} [MetricSpace E₁] [MetricSpace E₂]
    (F : (ℝ≥0 → E₁) → (ℝ≥0 → E₂)) (hF : ∀ x, IsCadlag x → IsCadlag (F x))
    (hequiv : ∀ x l, IsCadlag x → IsTimeChange l → F (x ∘ l) = F x ∘ l) :
    ((∀ (xs : ℕ → ℝ≥0 → E₁) (x : ℝ≥0 → E₁), (∀ n, IsCadlag (xs n)) → IsCadlag x →
        TendstoUniformlyOnBounded xs x → SkorohodTendsto (fun n => F (xs n)) (F x)) →
      ∀ (xs : ℕ → ℝ≥0 → E₁) (x : ℝ≥0 → E₁), SkorohodTendsto xs x →
        SkorohodTendsto (fun n => F (xs n)) (F x)) ∧
    ((∀ (xs : ℕ → ℝ≥0 → E₁) (x : ℝ≥0 → E₁), (∀ n, IsCadlag (xs n)) → IsCadlag x →
        TendstoUniformlyOnBounded xs x → TendstoUniformlyOnBounded (fun n => F (xs n)) (F x)) →
      ∀ (xs : ℕ → ℝ≥0 → E₁) (x : ℝ≥0 → E₁), SkorohodTendsto xs x →
        SkorohodTendsto (fun n t => (xs n t, F (xs n) t)) (fun t => (x t, F x t))) := by sorry

end KurtzProtter91.Integrals
