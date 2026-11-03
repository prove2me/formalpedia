-- Prove2me | Theorems.Thm_MultiPurchaseMNL_evaluator_exact
-- name    : MultiPurchaseMNL.evaluator_exact
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:13:57.354488+00:00
-- url     : https://prove2.me/theorems/76f4e11b-58f6-4038-94f3-c68e8b361282
-- title:
--   §2.2, p.11 — the recursion of Lemma 1 computes $\pi_m$, $\pi$ and $\mathcal R$ exactly
-- statement:
--   Under the Multi-Purchase MNL model with standard Gumbel shocks and positive weights:
--
--   1. for every $m\ge0$, every assortment $S$ and every $i\in S$, the recursion of Lemma 1 started at $\hat\pi_0=0$ gives the choice probability: $\pi_m(i,S)=\hat\pi_m(i,S)$;
--   2. the program's evaluator `evalR`, run on a list $l$ of distinct products, returns exactly the expected revenue
--   $$
--   \mathcal R(S)=\sum_{i\in S}r_i\sum_{m=0}^{m_{\max}}\Pr[M=m]\,\pi_m(i,S),\qquad S=\{l\}.
--   $$
--
--   This is the paper's remark that choice probabilities can be computed through the recursive expression of Lemma 1. It is what lets the algorithm of Theorem 1 compare its candidates by their true expected revenue.
--
--   Differences from the source:
--
--   - reading: computing π(i,S) via the recursive expression of Lemma 1 requires evaluating πₘ(Ŝ) for Ŝ ⊆ S, m ≤ |Ŝ| → πₘ = π̂ₘ for i ∈ S, and the instrumented evaluator evalR returns R exactly; reason: the sentence asserts that the recursion computes the choice probabilities; Theorem 1's program uses that computation
--   - generalization: m ≤ |Ŝ| → every m : ℕ; reason: specializes to m ≤ |Ŝ|
--   - encoding: assortments as sets → evalR reads an assortment as a list without repetition, compared with R of its Finset; reason: the same assortments
--   - encoding: products 1..n and the no-purchase option 0; Uᵢ = vᵢ + eᵢ with e₀,…,eₙ i.i.d. standard Gumbel (0,1), v₀ = 0; wᵢ = e^{vᵢ} → products Fin n, option 0 = none : Option (Fin n); shocks under Measure.pi of μ with IsExtremeValue μ; vᵢ = log wᵢ with wᵢ > 0, so w₀ = 1; reason: same model: wᵢ = e^{vᵢ} > 0 is exactly vᵢ = log wᵢ, and IsExtremeValue is the standard Gumbel cdf
--   - encoding: M supported on {0, 1, …, m_max} (§4, p.16), π(i,S) = Σ_{m∈[n]} Pr[M = m]·πₘ(i,S); m_max = O(1) presupposes m_max ≥ 1 → p : Fin (m_max+1) → ℝ with p ≥ 0, Σ p = 1; π(i,S) = Σ_{m=0}^{m_max} pₘ·πₘ(i,S) with π₀ = 0; Standing contains 1 ≤ m_max; reason: same distributions of M; the m = 0 term vanishes, and at m_max = 0 every revenue is 0 (p.12: one may assume Pr[M > 0] = 1)
-- source:
--   Bai, Feldman, Segev, Topaloglu, Wagner, Assortment Optimization under the Multi-Purchase Multinomial Logit Choice Model, author manuscript (Apr 2023), §2.2, p.11, "via the recursive expression of Lemma 1"

import Mathlib
import Definitions.Def_McFadden1974_RandomUtility_Model
import Definitions.Def_MultiPurchaseMNL_Model
import Definitions.Def_MultiPurchaseMNL_ValueFunction
import Definitions.Def_MultiPurchaseMNL_Algorithm

open MeasureTheory ProbabilityTheory

namespace MultiPurchaseMNL

/-- Bai, Feldman, Segev, Topaloglu, Wagner, *Assortment Optimization under the Multi-Purchase
Multinomial Logit Choice Model*, author manuscript (Apr 2023), §2.2, p.11: "computing choice
probabilities of the form `π(i,S) = Σ_{m∈[n]} Pr[M = m] · πm(i,S)` via the recursive expression of
Lemma 1 requires evaluating `πm(Ŝ)` for all assortments `Ŝ ⊆ S` with `i ∈ Ŝ` and for all `m ≤ |Ŝ|`".

Two statements:
1. for every `m`, every assortment `S` and every `i ∈ S`, the recursion of Lemma 1 started at
   `π₀ = 0` (`piRec`) equals the choice probability (1): `πₘ(i, S) = π̂ₘ(i, S)`;
2. the program's evaluator `evalR`, run on a list `l` of distinct products, returns exactly the
   expected revenue `R(S)` of (2) for `S = {l}`.

**Formalization Note.** Part 2 is what lets the program of Theorem 1 compare candidates by their
true expected revenue. -/
theorem evaluator_exact (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : McFadden1974.RandomUtility.IsExtremeValue μ) {n mmax : ℕ} (I : Instance n mmax)
    (hw : ∀ i, 0 < I.w i) :
    (∀ (m : ℕ) (S : Finset (Fin n)) (i : Fin n), i ∈ S → piM μ I m i S = piRec I i m S) ∧
      (∀ l : List (Fin n), l.Nodup → ((evalR I l).run 0).1 = R μ I l.toFinset) := by sorry

end MultiPurchaseMNL
