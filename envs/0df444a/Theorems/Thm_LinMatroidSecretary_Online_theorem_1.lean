-- Prove2me | Theorems.Thm_LinMatroidSecretary_Online_theorem_1
-- name    : LinMatroidSecretary.Online.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:15:58.811192+00:00
-- url     : https://prove2.me/theorems/2c5556d9-3532-483f-81bd-4af5a8504263
-- title:
--   Theorem 1 — a 1/e-probability-competitive ordinal algorithm for linear matroids revealed online over a finite field
-- statement:
--   Let $F$ be a finite field, $d$ the length of the vectors and $n$ the number of elements. There is an ordinal online policy — valid, i.e. with all acceptance probabilities in $[0,1]$, and fixed before the instance — with the following property. For every finite ground set $R$ of $n$ elements, every value order on $R$ (weights with ties broken by a fixed total order) and every family of vectors $v:R\to F^d$, when the elements arrive in uniformly random order revealing their vectors and their relative value order:
--
--   1. the selected set $\mathrm{ALG}$ is always independent in the linear matroid of $v$;
--   2. every element of the greedy optimum is selected with probability at least $1/e$:
--   $$\Pr[e\in\mathrm{ALG}]\ \ge\ \frac1e\qquad\text{for every }e\in\mathrm{OPT}(R);$$
--   3. consequently, for every nonnegative weight function $w$ compatible with the value order,
--   $$\mathbb E[w(\mathrm{ALG})]\ \ge\ \frac{w(\mathrm{OPT}(R))}{e}.$$
--
--   The constant $1/e$ is the best possible guarantee for every number of arrivals already in the rank-one case (the classical secretary problem). This settles the strong (probability-competitive) matroid secretary conjecture for linear matroids in the online-representation model.
--
--   Differences from the source:
--   - encoding: weights w(e) with ties broken by a fixed total order on E → a LinearOrder on the ground type (the value order); clause 3 quantifies over every w ≥ 0 with w r ≤ w q whenever r < q; reason: every weighted instance with its tie-break is such a pair and conversely; OPT and an ordinal algorithm depend only on the order
--   - generalization: there is an ordinal online algorithm (any internal randomness) → there is a policy with behavioural randomness that sees only n, d, the observed vectors, their relative order and its own past decisions; reason: an existence claim over a smaller class of algorithms implies the source's claim
--   - encoding: the algorithm knows the number of elements and the field in advance → the policy is indexed by n, d and F; reason: d is revealed by the first arriving vector, so knowing it in advance changes nothing
--   - encoding: always selects an independent set ALG → every (σ, b) of positive probability yields an independent ALG(σ, b); reason: outcomes of probability zero never occur
--   - encoding: probability over the uniform arrival order and the internal randomness → exact finite sums (1/n!) Σ_σ Σ_b Pr[b | σ] · 1[…]; reason: finite probability space; no measure theory needed
--   - encoding: acceptance probabilities for genuine online histories up to n arrivals → Policy.Valid requires probabilities for all steps and all input comparison patterns, including unrealizable histories; reason: this is a total completion of the rule; the chosen feasible LP coordinates lie in [0,1] and unused coordinates are zero, so it adds no condition on an instance
-- source:
--   Kristóf Bérczi, Shaddin Dughmi, Vasilis Livanos, Jose Soto, Victor Verdugo, The Strong Secretary Conjecture is True for Linear Matroids, STOC 2027 submission #608 (October 2026), Theorem 1, PDF p. 3 (printed p. 1); proof §2.3, PDF p. 12 (printed p. 10)

import Mathlib
import Definitions.Def_LinMatroidSecretary_Online_Setting

namespace LinMatroidSecretary.Online

universe u

/-- Theorem 1 (PDF p. 3, printed 1; proof §2.3, PDF p. 12). Fix a finite field `F`, the vector
length `d` and the number of elements `n`. There is an ordinal online policy (its acceptance
probabilities lie in `[0,1]`), chosen before the instance, such that for every finite ground
type `R` with `n` elements, every value order on `R` and every vector family `v : R → F^d`:
1. every selected set that occurs with positive probability is independent;
2. every `e ∈ OPT(R)` is selected with probability at least `1/e`;
3. for every nonnegative weight function `w` that is monotone in the value order,
   `E[w(ALG)] ≥ w(OPT(R))/e`. -/
theorem theorem_1 (F : Type*) [Field F] [Fintype F] (d n : ℕ) :
    ∃ π : Policy n d F, π.Valid ∧
      ∀ (R : Type u) [Fintype R] [LinearOrder R], Fintype.card R = n →
      ∀ v : R → Fin d → F,
        (∀ (σ : Fin n ≃ R) (b : Fin n → Bool), 0 < runProb π v σ b →
          LinearIndepOn F v (alg σ b : Set R)) ∧
        (∀ e ∈ OPT F v Finset.univ, Real.exp (-1) ≤ selProb π v e) ∧
        (∀ w : R → ℝ, (∀ r, 0 ≤ w r) → (∀ r q, r < q → w r ≤ w q) →
          (∑ e ∈ OPT F v Finset.univ, w e) * Real.exp (-1) ≤ expWeight π v w) := by sorry

end LinMatroidSecretary.Online
