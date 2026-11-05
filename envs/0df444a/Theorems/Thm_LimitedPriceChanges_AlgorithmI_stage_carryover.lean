-- Prove2me | Theorems.Thm_LimitedPriceChanges_AlgorithmI_stage_carryover
-- name    : LimitedPriceChanges.AlgorithmI.stage_carryover
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T19:06:32.938367+00:00
-- url     : https://prove2.me/theorems/905eebca-e3a4-4abf-9d2d-60db8993ae1f
-- title:
--   Proof of Theorem 1, third part of (23) — carried-in inventory makes $y_t\ne\tilde y_i$ in only $O(1)$ expected periods per stage
-- statement:
--   Consider Algorithm-I with $m\ge1$ price changes on the censored pricing–inventory model of §2–§3, under the standing hypotheses at the true parameter $z$ ($\mathbb E[D(p,z)]>0$, Assumption A, every optimal order-up-to level exceeds $d^l$, Definition 1, Assumption 1) and with valid inputs and selections. In stage $i\in\{1,\dots,m+1\}$ the algorithm fixes the price $\hat p_i$ and the target $\tilde y_i$ (Step 1), and in each period $t$ of the stage orders up to
--   $$y_t=\max\{x_t,\tilde y_i\},$$
--   where $x_t$ is the inventory carried into period $t$. In particular, when the inventory carried over from stage $i-1$ exceeds the new target $\tilde y_i$, the order-up-to level differs from $\tilde y_i$ until that inventory has been sold down.
--
--   There is a constant $K>0$ such that, for all large enough $T$ and every stage $i\in\{1,\dots,m+1\}$,
--   $$\mathbb E\Big[\#\{t\in\text{stage } i:\ y_t\ne\tilde y_i\}\Big]\le K .$$
--
--   This is the inventory carry-over ingredient of the third part of the regret decomposition (23) in the proof of Theorem 1 (pp. 24–25): together with (26) it controls the expected number of periods of stages $i\ge2$ in which the implemented level $y_t$ differs from the plug-in level $\hat y_i$.
--
--   **Formalization Note** The expectation is the sum over demand paths $d\in\mathbb N^T$ weighted by the path law $\prod_t f(d_t;p_t,z)$ of Algorithm-I (`Alg.expect`), and the count is $\sum_{s<T}\mathbf 1\{\mathrm{stage}(s)=i,\ y_s\ne\tilde y_i\}$ in $[0,\infty]$. Stages are 1-based and periods 0-based, as in the definition `LimitedPriceChanges_AlgorithmI_Algorithm`.
-- source:
--   Chen, Chao and Wang, Data-Based Dynamic Pricing and Inventory Control with Censored Demand and Limited Price Changes, SSRN 2700747 (revision of 2020-02-10), proof of Theorem 1, pp. 24–25 (third part of the decomposition (23)); Algorithm-I Step 1, p. 9 (y_t = max{x_t, ỹ_i})

import Mathlib
import Definitions.Def_LimitedPriceChanges_AlgorithmI_Algorithm

namespace LimitedPriceChanges.AlgorithmI

/-- **Carried-in inventory is depleted in `O(1)` expected periods** (used in the third part of
(23), proof of Theorem 1, pp. 24–25). There is a constant `K > 0` such that, for `T` large
enough and every stage `i ∈ {1, …, m + 1}`, the expected number of periods `s` of stage `i` whose
order-up-to level `y_s = max{x_s, ỹᵢ}` differs from the stage target `ỹᵢ` (i.e. the carried
inventory `x_s` exceeds `ỹᵢ`) is at most `K`. -/
theorem stage_carryover (S : Model) (A : Alg S) (z : ℝ) (hS : S.Standing A.pstar z)
    (hA : A.Valid) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀, ∀ i ∈ Finset.Icc 1 (A.m + 1),
      A.expect z T (fun d => ∑ s : Fin T,
          if A.stageOf T s = i ∧ A.level T s d ≠ A.ytilde T i d then (1 : ENNReal) else 0) ≤
        ENNReal.ofReal K := by sorry

end LimitedPriceChanges.AlgorithmI
