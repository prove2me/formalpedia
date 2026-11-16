-- Prove2me | Theorems.Thm_GaussPart_Supplement_theorem_7_3
-- name    : GaussPart.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:13:58.006803+00:00
-- url     : https://prove2.me/theorems/9833b3e3-c2c4-4085-a0fc-0edd96b9cfaa
-- title:
--   Theorem 7.3 — SQ lower bound $d^{\Omega(1/\epsilon^2)}$ for realizable PQ and TDS learning of intersections of two halfspaces
-- statement:
--   **Setting.** Let $\mathcal F$ be the class of intersections of two halfspaces over $\mathbb R^d$, and $P=\mathcal N(0,I_d)$ the training marginal. A learner has SQ access to the labeled training distribution, the law of $(x,f(x))$ with $x\sim P$, and to an arbitrary unlabeled test distribution $Q$.
--
--   - **$(\epsilon,\delta)$-PQ learning**: for every target $f\in\mathcal F$ and every $Q$, return $h:\mathbb R^d\to\{\pm1,\bot\}$ such that with probability at least $1-\delta$, $\Pr_P[h(x)=\bot]\le\epsilon$ and $\Pr_Q[h(x)\neq f(x),\,h(x)\neq\bot]\le\epsilon$.
--   - **$(\epsilon,\delta)$-TDS learning**: reject, or accept with $h:\mathbb R^d\to\{\pm1\}$; if $Q=P$ it accepts with probability at least $1-\delta$, and with probability at least $1-\delta$, whenever it accepts, $\Pr_Q[h(x)\neq f(x)]\le\epsilon$.
--
--   **Theorem.** There are universal constants $c,c'>0$ such that for every sufficiently small $\epsilon>0$ and sufficiently large $d$ (depending on $\epsilon$), any algorithm that $(\epsilon,1/20)$-PQ learns or $(\epsilon,1/20)$-TDS learns $\mathcal F$ under $\mathcal N(0,I_d)$ with SQ access to both distributions must either make at least
--   $$
--   2^{d^{c'}}\ \text{queries in total}\qquad\text{or a query to either oracle of tolerance at most}\qquad d^{-c/\epsilon^2}.
--   $$
--
--   This separates realizable PQ/TDS learning from agnostic reliable learning (Theorem 6.2) in the Gaussian setting.
--
--   **Formalization Note** A two-oracle SQ algorithm asks one-sided queries on $(\mathbb R^d\times\mathbb R)\sqcup\mathbb R^d$; the statement is given for each kind of learner, with the same constants.
--
--   Differences from the source:
--   - encoding: any SQ algorithm (Definition A.4) that makes no query of tolerance at most τ₀ → every randomized adaptive SQ algorithm of the published SQAlg type whose every query is a measurable [−1,1]-valued function with tolerance > τ₀, against adversarial trajectory-dependent oracles; reason: the published SQ model; states no run reaches can be changed without changing any run
--   - reading: requires 2^{d^{Ω(1)}} queries → on some admissible instance, against some valid oracle, some run makes at least 2^{d^{c₁}} queries with positive probability; reason: worst-case query complexity of a randomized SQ algorithm
--   - encoding: SQ access to the labeled training distribution and the unlabeled test distribution → one SQAlg on (ℝ^d × ℝ) ⊕ ℝ^d with one-sided queries, valid for train mapped to the left summand plus Q mapped to the right; reason: a one-sided query has exactly one oracle's expectation as its integral
--   - encoding: selective hypothesis h : ℝ^d → {±1, ⊥}; reject or (accept, h) → h : ℝ^d → Option ℝ with none for ⊥; outputs Option (ℝ^d → ℝ) with none for reject; reason: a non-±1 value counts as an error
--   - reading: with probability at least 1 − δ, whenever it accepts, Pr_Q[h ≠ f] ≤ ϵ → the probability of stopping with an accepted h with Pr_Q[h ≠ f] > ϵ is at most 1/20; reason: a run that does not stop does not accept
--   - encoding: intersections of two halfspaces; sufficiently small ϵ; sufficiently large d depending on ϵ → IntersectionClass d 2 (closed halfspaces, at most two); ∃ ϵ₀ > 0, and for each ϵ ≤ ϵ₀ some d₀(ϵ); reason: a single halfspace or a constant is an intersection of two halfspaces
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Theorem 7.3, p.64 (PDF p.66); Definitions 7.1, 7.2, p.63 (PDF p.65)

import Mathlib
import Definitions.Def_PrivLearn_SQSim_SQAlg
import Definitions.Def_GaussPart_Supplement_Halfspaces
import Definitions.Def_GaussPart_Supplement_SQ

open MeasureTheory ProbabilityTheory PrivLearn.SQSim

namespace GaussPart

namespace Supplement

/-- **Theorem 7.3** (SQ Lower Bound for PQ and TDS learning).

I. Diakonikolas, G. Iakovidis, D. M. Kane, M. Ma, *Gaussian Partitioning for Reliable Learning of
Multi-Index Models*, arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Theorem 7.3, p.64 (PDF p.66);
Definitions 7.1 and 7.2, p.63 (PDF p.65).

"Let F be the class of intersections of two halfspaces over ℝ^d. There exist universal constants
c, c′ > 0 such that, for every sufficiently small ϵ > 0 and sufficiently large d depending on ϵ, the
following holds. Any algorithm (ϵ, 1/20)-PQ learns or (ϵ, 1/20)-TDS learns F under N(0, I), using SQ
access to the labeled training distribution and the unlabeled test distribution, must either make at
least 2^{d^{c′}} SQ queries in total or make a query to either oracle of tolerance at most
d^{−c/ϵ²}."

**Formalization Note.**
* `F = IntersectionClass d 2` (at most two closed halfspaces; the proof's target `2·1{|v·x| ≤ t} − 1` is
  an intersection of two closed halfspaces). `c, c′` come first, then the threshold `ϵ₀` of
  "sufficiently small ϵ", then for each `ϵ` the threshold `d₀(ϵ)`.
* The training law for target `f` is the law of `(x, f(x))`, `x ∼ N(0, I_d)`. A two-oracle SQ algorithm
  is a published `SQAlg` on `(ℝᵈ × ℝ) ⊕ ℝᵈ` whose queries are `OneSided`; its oracle is valid for
  `twoOracleMeasure train Q`, i.e. a valid training oracle and a valid test oracle at once.
  `TolAbove` bounds the tolerance of queries to both oracles; the query count is the total.
* **PQ** (Definition 7.1): outputs `h : ℝᵈ → Option ℝ` (`none` is `⊥`); for every `f ∈ F`, every test
  law `Q` and every valid oracle, with probability `≥ 1 − 1/20` it outputs `h` with
  `Pr_{N(0,I)}[h = ⊥] ≤ ϵ` and `Pr_Q[h ≠ f, h ≠ ⊥] ≤ ϵ`.
* **TDS** (Definition 7.2): outputs `none` (reject) or `some h` (accept with `h`). Completeness: for
  `Q = N(0, I_d)` it accepts with probability `≥ 1 − 1/20`. Soundness: for every `Q`, the probability of
  accepting an `h` with `Pr_Q[h ≠ f] > ϵ` is at most `1/20`.
* The conclusion is stated for each kind of algorithm separately, with the same `c, c′`. -/
theorem theorem_7_3 :
    ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
    (∀ (St : Type) (B : SQAlg ((Vec d × ℝ) ⊕ Vec d) (Vec d → Option ℝ) St),
      OneSided B → TolAbove B ((d : ℝ) ^ (-c / ε ^ 2)) →
      (∀ f ∈ IntersectionClass d 2, ∀ Q : Measure (Vec d), IsProbabilityMeasure Q →
        ∀ O : List St → ℝ,
          B.IsValidOracle
            (twoOracleMeasure ((stdGaussian (Vec d)).map fun x => (x, f x)) Q) O →
          (19 / 20 : ENNReal) ≤ successMass B O
            {h | stdGaussian (Vec d) {x | h x = none} ≤ ENNReal.ofReal ε ∧
              Q {x | h x ≠ none ∧ h x ≠ some (f x)} ≤ ENNReal.ofReal ε}) →
      ∃ f ∈ IntersectionClass d 2, ∃ Q : Measure (Vec d), IsProbabilityMeasure Q ∧
        ∃ O : List St → ℝ,
          B.IsValidOracle
            (twoOracleMeasure ((stdGaussian (Vec d)).map fun x => (x, f x)) Q) O ∧
          MakesManyQueries B O ((2 : ℝ) ^ ((d : ℝ) ^ c'))) ∧
    (∀ (St : Type) (B : SQAlg ((Vec d × ℝ) ⊕ Vec d) (Option (Vec d → ℝ)) St),
      OneSided B → TolAbove B ((d : ℝ) ^ (-c / ε ^ 2)) →
      (∀ f ∈ IntersectionClass d 2, ∀ O : List St → ℝ,
          B.IsValidOracle (twoOracleMeasure ((stdGaussian (Vec d)).map fun x => (x, f x))
            (stdGaussian (Vec d))) O →
          (19 / 20 : ENNReal) ≤ successMass B O {o | o ≠ none}) →
      (∀ f ∈ IntersectionClass d 2, ∀ Q : Measure (Vec d), IsProbabilityMeasure Q →
        ∀ O : List St → ℝ,
          B.IsValidOracle
            (twoOracleMeasure ((stdGaussian (Vec d)).map fun x => (x, f x)) Q) O →
          successMass B O {o | ∃ h, o = some h ∧ ENNReal.ofReal ε < Q {x | h x ≠ f x}} ≤
            1 / 20) →
      ∃ f ∈ IntersectionClass d 2, ∃ Q : Measure (Vec d), IsProbabilityMeasure Q ∧
        ∃ O : List St → ℝ,
          B.IsValidOracle
            (twoOracleMeasure ((stdGaussian (Vec d)).map fun x => (x, f x)) Q) O ∧
          MakesManyQueries B O ((2 : ℝ) ^ ((d : ℝ) ^ c'))) := by sorry

end Supplement

end GaussPart
