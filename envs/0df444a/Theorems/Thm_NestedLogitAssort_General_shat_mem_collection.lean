-- Prove2me | Theorems.Thm_NestedLogitAssort_General_shat_mem_collection
-- name    : NestedLogitAssort.General.shat_mem_collection
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T18:53:27.609729+00:00
-- url     : https://prove2.me/theorems/ae1d81dc-788a-46f0-bf9b-5d41aa91b598
-- title:
--   Section 5: every greedy assortment $\hat S_i(\epsilon_i)$ is some $N^k_{ij}$
-- statement:
--   Fix a nest $i$ with $n\ge1$ products of nonnegative preference weights, sorted by nonincreasing revenue, and a listing $\sigma$ of the products by nondecreasing weight. Let $\hat S_i(\epsilon)$ be the set of products that the greedy fill of the continuous knapsack (11) with capacity $\epsilon$ takes entirely. Then
--
--   $$
--   \{\hat S_i(\epsilon):\epsilon\in[0,\infty]\}\ \subseteq\ \{N^k_{ij}:k=1,\dots,n,\ j=0,\dots,k\}:
--   $$
--
--   1. for every $\epsilon\ge0$ there are $1\le k\le n$ and $0\le j\le k$ with $\hat S_i(\epsilon)=N^k_{ij}$;
--   2. $\hat S_i(\infty)=N=N^n_{in}$.
--
--   This is why the collection of Theorem 11 contains the candidates of Theorem 10, so that the factor-two argument of Theorem 10 is available inside the proof of Theorem 11.
--
--   Differences from the source:
--   - reading: "the only possible values for k are k = 1, …, n" → hypothesis 0 < n; reason: the range k = 1, …, n presupposes n ≥ 1
--   - generalization: N^k_ij is built from "the products with the k smallest preference weights" (p. 25), which is not unique when weights are tied → every listing σ_i of the products of nest i by nondecreasing weight (IsWeightOrder), one per nest, universally quantified; reason: covers every tie-break the paper could mean; with distinct weights there is exactly one such σ_i and the statement is the paper's
--   - encoding: N^k_ij: "the first j products with the largest revenues" among the k lightest products → NK σ k j: the j smallest indices of Light σ k; reason: products are indexed in nonincreasing revenue order (p. 7), so this is a revenue order with ties broken by index; NK σ n j = N_ij as on p. 26
--   - encoding: Ŝ_i(ϵ_i) = {j : ẑ_ij(ϵ_i) = 1}, ẑ_i(ϵ_i) the greedy fill of (11) in revenue order among products with v_ij ≤ ϵ_i → Shat: eligible products (v_ij ≤ ϵ) taken in index order while they fit entirely; the fill stops at the first one that does not fit, so a later zero-weight product is not taken; reason: the page does not say whether zero-weight products after the fractional item get 1; they change neither Σ r v nor V_i, so every constraint value of (3) and (4) is the same under either convention, and under the stop rule Ŝ_i(ϵ) is an N^k_ij as p. 25 asserts
--   - encoding: ϵ_i ∈ [0, ∞] → Ŝ_i(ϵ) for real ϵ ≥ 0, plus N (Finset.univ) for ϵ = ∞; reason: with infinite capacity every product is eligible and fits, so Ŝ_i(∞) = N
--   - reading: v_ij are preference weights (p. 7 allows padding products with v_ij = 0) → hypothesis 0 ≤ v_ij (zero allowed); reason: preference weights of a logit model are nonnegative; the remarks on p. 7 allow exactly the zero values
--   - generalization: products ordered so that r_i1 ≥ … ≥ r_in (p. 7), and Ŝ_i(ϵ_i) filled in that revenue order → no ordering of the revenues assumed; Shat fills in index order; reason: the inclusion uses only the weights and the index order; under r_i1 ≥ … ≥ r_in the index order is the page's revenue order, so it specializes to the page
--   - encoding: products N = {1, …, n} → products Fin n (index 0 is product 1); 1-based k and j are natural numbers; reason: Lean convention; same instances
-- source:
--   Davis, Gallego & Topaloglu, Assortment Optimization under Variants of the Nested Logit Model, revised manuscript of June 18, 2013, Section 5, p. 25

import Mathlib
import Definitions.Def_NestedLogitAssort_General_Shat
import Definitions.Def_NestedLogitAssort_General_NK
import Definitions.Def_NestedLogitAssort_General_IsWeightOrder

namespace NestedLogitAssort.General

/-- **Every greedy assortment `Ŝ_i(ϵ_i)` is some `N^k_{ij}`.**
Davis, Gallego & Topaloglu, *Assortment Optimization under Variants of the Nested Logit Model*,
revised manuscript of June 18, 2013, Section 5, p. 25 (unnumbered): "Therefore, `Ŝ_i(ϵ_i)` must be one of the assortments
`{N^k_{ij} : j = 0, …, k}`, where we let `N^k_{i0} = ∅` for notational uniformity. Since the only
possible values for `k` are `k = 1, …, n`, it follows that
`{Ŝ_i(ϵ_i) : ϵ_i ∈ [0, ∞]} ⊂ {N^k_{ij} : k ∈ N, j = 0, …, k}`."

For every listing `σ` of the products of nest `i` by nondecreasing weight: every `Ŝ_i(ϵ)` with
`ϵ ≥ 0` equals `N^k_{ij}` for some `1 ≤ k ≤ n` and `0 ≤ j ≤ k`, and `Ŝ_i(∞) = N` equals `N^n_{in}`.

**Formalization Note.** `ϵ_i = ∞` is the second conjunct: with infinite capacity every product is
eligible and fits, so `Ŝ_i(∞) = N`. Hypotheses: `n ≥ 1` (so `k = 1, …, n` exists), `v_{ij} ≥ 0`. -/
theorem shat_mem_collection {M : Type*} {n : ℕ} (I : Instance M n) (i : M) (hn : 0 < n)
    (hv : ∀ j, 0 ≤ I.v i j) (σ : Equiv.Perm (Fin n)) (hσ : IsWeightOrder I i σ) :
    (∀ ε : ℝ, 0 ≤ ε → ∃ k j : ℕ, 1 ≤ k ∧ k ≤ n ∧ j ≤ k ∧ Shat I i ε = NK σ k j) ∧
      (Finset.univ : Finset (Fin n)) = NK σ n n := by sorry

end NestedLogitAssort.General
