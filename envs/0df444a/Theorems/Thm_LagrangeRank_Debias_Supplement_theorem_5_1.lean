-- Prove2me | Theorems.Thm_LagrangeRank_Debias_Supplement_theorem_5_1
-- name    : LagrangeRank.Debias.Supplement.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:55:35.877723+00:00
-- url     : https://prove2.me/theorems/0ef2841d-e826-42fe-b5b6-7558778b4622
-- title:
--   Theorem 5.1 (Necessary Signal Strength): minimax risk above 1 − ε below the rate (5.2)
-- statement:
--   Consider the BTL model with comparison graph $G(n,p)$ and $L$ comparisons per observed edge. For ranking properties $R_1,\dots,R_n$ (Definition 2.3), a swap-closed parameter set $\Xi$, the signal $\Delta(\theta)$ of (4.2), divider sets (Definition 5.1) and the minimax risk $\mathfrak R$ of (5.1):
--
--   There are constants $C_0>0$ and $c>0$ such that for every $\varepsilon>0$, all $n,L$, every $p\ge C_0\log n/n$, all properties and every swap-closed $\Xi$: if some $\theta\in\Xi$ with a divider set $M(\theta)$ satisfies
--   $$\Delta(\theta)\le c\sqrt{\frac{\varepsilon\log(|M(\theta)|+1)-\log 2}{npL}},$$
--   then
--   $$\mathfrak R=\inf_\psi\sup_{\theta^*\in\Xi}P\big(\#\text{false positives}+\#\text{false negatives}\ge1\big)>1-\varepsilon .$$
--
--   This is the information-theoretic lower bound matching the power thresholds of Sections 3–4: below the rate, no procedure controls the probability of making at least one error. When the radicand is not positive the real square root is $0$, and the premise cannot hold because $\Delta(\theta)>0$ (a legal pair never has tied scores).
--
--   Differences from the source:
--   - reading: Δ(θ) ≲ √((ε log(|M(θ)|+1) − log 2)/(npL)) in the premise → Δ(θ) ≤ c·√(…) for one absolute constant c > 0 chosen before ε, n, L, p, the properties, Ξ, θ and M; reason: ≲ (p. 8) hides a constant; in the premise of a lower bound it must be a sufficiently small constant, the literal "some C > 0" reading being false; choosing c before ε is the strongest reading
--   - reading: p ≳ log n/n → p ≥ C0 log n/n for one constant C0 > 0 chosen first; reason: as in Theorem 3.2 and Lemma 3.1, ≳ denotes a fixed constant multiple
--   - generalization: Ξ is the BTL parameter space (bounded dynamic range, Section 2.1), closed under swaps → Ξ is any swap-closed set of score vectors; reason: the BTL parameter space with bounded dynamic range is swap-closed, so the statement specializes to the source
--   - encoding: if there exists θ ∈ Ξ (with its divider set M(θ)) satisfying (5.2) → for every θ ∈ Ξ and every divider set M of θ, the premise (5.2) implies the conclusion; reason: an existential antecedent is the same as a universal premise; the divider set is not unique, so every one is allowed
--   - encoding: a selection procedure ψ → any function of the observed data (graph and outcomes on observed edges) into {0,1}^n; risk = worst-case probability that ψ ≠ ψ*; reason: # false positives + # false negatives ≥ 1 exactly when ψ ≠ ψ*; the data space is finite so every such function is measurable
--   - encoding: rankings without a tie rule → increasing-index tie resolution; reason: used throughout the mission for γ(θ); legal pairs never have tied scores
-- source:
--   Liu, Fang, Lu, Lagrangian Inference for Ranking Problems, arXiv:2110.00151v1, p. 29, Theorem 5.1; (5.1) and Definition 5.1, p. 28

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Supplement_LowerBound

namespace LagrangeRank.Debias.Supplement

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ENNReal
/-- Necessary signal strength: below c times the rate (5.2), every selection procedure has
minimax risk above 1 − ε. -/
theorem theorem_5_1 :
    ∃ C0 c : ℝ, 0 < C0 ∧ 0 < c ∧
    ∀ ε : ℝ, 0 < ε →
    ∀ (n L : ℕ) (p : unitInterval) (R : Fin n → Set (Ranking n)) (Ξ : Set (Vec n)),
      (∀ i, RankingProperty i (R i)) → SwapClosed Ξ →
      C0 * Real.log n / n ≤ (p : ℝ) →
      ∀ θ ∈ Ξ, ∀ M : Finset (Fin n × Fin n), IsDividerSet θ R M →
      familySignal θ R ≤ ENNReal.ofReal (c * Real.sqrt
        ((ε * Real.log ((M.card : ℝ) + 1) - Real.log 2) / ((n : ℝ) * p * L))) →
      1 - ε < minimaxRisk L p R Ξ := by sorry

end LagrangeRank.Debias.Supplement
