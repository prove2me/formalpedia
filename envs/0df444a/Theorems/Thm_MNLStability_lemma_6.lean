-- Prove2me | Theorems.Thm_MNLStability_lemma_6
-- name    : MNLStability.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:31:07.849263+00:00
-- url     : https://prove2.me/theorems/5cf33298-2f66-42db-8ac6-4fe5ef2efaf9
-- title:
--   Lemma 6 — rearranging a uniform-weight class to be monotone in price
-- statement:
--   Let $I$ be a set of products with uniform preference weights, indexed by non-increasing prices $r_1\ge\dots\ge r_m$. For every inventory vector $U$ there is a vector $V^\uparrow$ with $V^\uparrow_1\ge\dots\ge V^\uparrow_m$ such that $U^\uparrow=U\hookleftarrow_I V^\uparrow$ satisfies:
--
--   1. $\mathbb E[X_i^{U^\uparrow}]=\mathbb E[X_i^U]$ for every product $i\notin I$;
--   2. $\sum_{i\in I}r_i\,\mathbb E[X_i^{U^\uparrow}]\ \ge\ \sum_{i\in I}r_i\,\mathbb E[X_i^U]$;
--   3. $\|U^\uparrow\|_1=\|U\|_1$.
--
--   This is Transformation 1 of §4.2, the first step towards step-function inventories.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: U with at most C units (§4.1, p.18–19) → every inventory vector U; reason: the proof (exchanges) never uses the capacity; the paper's case is an instance
--   - encoding: I = [m] with r₁ ≥ ⋯ ≥ r_m → a list ord of the products of I with non-increasing prices; reason: Lean convention; same instances
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 6, p.19; proof App. A.2, pp.43–44

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsPriceOrder

namespace MNLStability

/-- **Lemma 6** (SSRN:3498325, p.19; proof App. A.2, pp.43–44). Let `I` be a set of products with
uniform preference weights, listed by `ord` by non-increasing price (`r₁ ≥ ⋯ ≥ r_m`, p.18). For
every inventory vector `U` there is a vector `V↑` with `V↑₁ ≥ ⋯ ≥ V↑_m` such that `U↑ = U ↩_I V↑`
satisfies:
1. `E[X_i^{U↑}] = E[X_i^U]` for every product `i ∉ I`;
2. `Σ_{i ∈ I} r_i E[X_i^{U↑}] ≥ Σ_{i ∈ I} r_i E[X_i^U]`;
3. `‖U↑‖₁ = ‖U‖₁`. -/
theorem lemma_6 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I)
    (ord : List (Fin n)) (hord : IsPriceOrder r I ord) (U : Fin n → ℕ) :
    ∃ V : Fin n → ℕ, NonincAlong ord V ∧
      (∀ i, i ∉ I → expX wts pM (swap I U V) i = expX wts pM U i) ∧
      ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM (swap I U V) i ∧
      norm1 (swap I U V) = norm1 U := by sorry

end MNLStability
