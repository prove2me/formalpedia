-- Prove2me | Theorems.Thm_MultiPurchaseMNL_theorem_1
-- name    : MultiPurchaseMNL.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:14:14.885017+00:00
-- url     : https://prove2.me/theorems/dffb0e62-e06f-42eb-935a-a3a4bf94a096
-- title:
--   Theorem 1 — a deterministic $O(n^{O(m_{\max}^2/\epsilon)})$-time algorithm within $1-\epsilon$ of optimal
-- statement:
--   Consider the Multi-Purchase MNL assortment problem with $n$ products, preference weights $w_i>0$, revenues $r_i$, standard Gumbel utility shocks, and a maximum number of purchases $M$ supported on $\{0,1,\dots,m_{\max}\}$ with $m_{\max}\ge1$. There are universal constants $C$ and $K$ such that for every $\varepsilon>0$ the deterministic program `ptas` (the algorithm of §4) returns an assortment $\tilde S$ with
--   $$
--   \mathcal R(\tilde S)\ \ge\ (1-\varepsilon)\,\mathcal R(S)\quad\text{for every assortment }S\subseteq[n],
--   $$
--   and performs at most $K\cdot\max(n,2)^{C\,m_{\max}^2/\varepsilon}$ unit-cost operations. In the paper's words: for any $\epsilon>0$, there is a deterministic $O(n^{O(m^2_{\max}/\epsilon)})$-time algorithm for computing an assortment whose expected revenue is within factor $1-\epsilon$ of optimal.
--
--   When $m_{\max}$ is a constant this is a polynomial-time approximation scheme for assortment optimization under the Multi-Purchase MNL model.
--
--   Differences from the source:
--
--   - reading: there is a deterministic algorithm → the explicit instrumented program ptas of §4 in the unit-cost real RAM (CapacitatedAssort.General.Work); reason: without a program and a cost model the claim holds trivially by returning an optimal assortment
--   - reading: O(n^{O(m²max/ϵ)}) → ∃ universal C, K : ℕ, quantified before every type and datum, with ops ≤ K·max(n,2)^{C·m²_max/ε}; reason: the meaning of the nested O-notation; max(n,2) reads n → ∞
--   - reading: §4.1: 1/ϵ an integer; (6): rounding to multiples of δW/n; §4.2: return S̃ for the right guess → the program runs at ε' = 1/⌈2/ε⌉₊, uses the grid δW/((1+δ)²n) with an explicit window, and returns the candidate of largest exact revenue (ties: first found); reason: the paper leaves these points informal (readings 3–5 of the mission); none weakens the guarantee
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
--   - generalization: m_max = O(1) with M over [n]₀; rᵢ > 0 → any m_max ≥ 1, not bounded by n; rᵢ ≥ 0; reason: specializes to the paper's instances
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), Theorem 1, p.16

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_Algorithm

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), **Theorem 1**, p.16: "For any
`ϵ > 0`, there is a deterministic `O(n^{O(m²max/ϵ)})`-time algorithm for computing an assortment whose
expected revenue is within factor `1 − ϵ` of optimal", when the maximum number of purchases `M` is
supported over `{0, 1, …, m_max}` (§4, p.16).

There are universal constants `C`, `K` such that:
1. for every standard Gumbel law `μ` of the shocks, every instance and every `ε > 0`, the assortment
   `S̃` returned by the program `ptas` satisfies `(1 − ε)·R(S) ≤ R(S̃)` for every assortment `S`;
2. for every instance and every `ε > 0`, `ptas` performs at most `K · max(n, 2)^{C·m²_max/ε}`
   unit-cost operations.

**Formalization Note.** "There is an algorithm" is read as a statement about the paper's algorithm of
§4, written as the deterministic instrumented program `ptas` (unit-cost real RAM: `+, −, ×, /`,
comparisons, `⌊·⌋₊`, `⌈·⌉₊`, array access); without the program the claim would hold by returning an
optimal assortment. `C`, `K` are quantified before every type and datum. The program runs at
`ε' = 1/⌈2/ε⌉₊`, uses the knapsack grid `δW/((1+δ)²n)` and returns the candidate of largest exact
revenue. Products are `Fin n`, `w₀ = 1`, `vᵢ = log wᵢ`, `Pr[M = m] = p m` on `{0, …, m_max}`,
`m_max ≥ 1`, `rᵢ ≥ 0`. -/
theorem theorem_1 :
    ∃ C K : ℕ,
      (∀ {n mmax : ℕ} (μ : Measure ℝ) [IsProbabilityMeasure μ],
        McFadden1974.RandomUtility.IsExtremeValue μ → ∀ (I : Instance n mmax), I.Standing →
          ∀ ε : ℝ, 0 < ε → ∀ S : Finset (Fin n), (1 - ε) * R μ I S ≤ R μ I (output I ε)) ∧
      (∀ {n mmax : ℕ} (I : Instance n mmax), I.Standing → ∀ ε : ℝ, 0 < ε →
        (ops I ε : ℝ) ≤ K * (max (n : ℝ) 2) ^ ((C : ℝ) * mmax ^ 2 / ε)) := by sorry

end MultiPurchaseMNL
