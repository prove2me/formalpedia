-- Prove2me | Theorems.Thm_MNLStability_lemma_7
-- name    : MNLStability.lemma_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:30:59.616828+00:00
-- url     : https://prove2.me/theorems/a71278d9-b1de-460b-845c-6c5fe643efb5
-- title:
--   Lemma 7 — rounding levels down to a $(1+\varepsilon)$-spaced set
-- statement:
--   Let $I$ be a set of products with uniform preference weights and $U$ a vector with at most $C$ units. Let $U^\uparrow$ agree with $U$ outside $I$ and satisfy the three properties of Lemma 6 with respect to $U$. Let $H$ be a $(1+\varepsilon)$-spaced subset of $[C]$ with $0$ added, $\varepsilon>0$, and $V^{\mathrm{step}}_i=\lfloor U^\uparrow_i\rfloor_H$ for $i\in I$. Then $U^{\mathrm{step}}=(U^\uparrow\hookleftarrow_I V^{\mathrm{step}})=(U\hookleftarrow_I V^{\mathrm{step}})$ satisfies:
--
--   1. $\mathbb E[X_i^{U^{\mathrm{step}}}]\ge\mathbb E[X_i^U]$ for every product $i\notin I$;
--   2. $\sum_{i\in I}r_i\,\mathbb E[X_i^{U^{\mathrm{step}}}]\ \ge\ (1-\varepsilon)\sum_{i\in I}r_i\,\mathbb E[X_i^U]$;
--   3. $\|U^{\mathrm{step}}\|_1\le\|U\|_1$.
--
--   This is Transformation 2 of §4.2: it leaves $O(\varepsilon^{-1}\log C)$ inventory levels on $I$.
--
--   Differences from the source:
--   - generalization: the standing assumption of §2.3, p.13 ("in the remainder of this paper, we operate under the opposite scenario of w_max > εw₀/n") → no regime hypothesis; reason: the proof uses no lower bound on purchase probabilities; every instance of the regime is covered
--   - generalization: U↑ the vector constructed in Lemma 6 → any U↑ agreeing with U outside I that satisfies properties 1–3 of Lemma 6; reason: the proof (App. A.3) uses only these properties of U↑; the vector of Lemma 6 is one such
--   - encoding: the number of customers M, finitely supported (p.3) → a law pM : ℕ →₀ ℝ (IsLaw) mixed over its support; reason: Lean convention; same instances
-- source:
--   Aouad & Segev, The Stability of MNL-Based Demand under Dynamic Customer Substitution and its Algorithmic Implications, SSRN:3498325 (manuscript of 2019-12-04), Lemma 7, p.19; proof App. A.3, pp.44–45

import Mathlib
import Definitions.Def_MNLStability_IsLaw
import Definitions.Def_MNLStability_expX
import Definitions.Def_MNLStability_opt
import Definitions.Def_MNLStability_swap
import Definitions.Def_MNLStability_IsSpaced

namespace MNLStability

/-- **Lemma 7** (SSRN:3498325, p.19; proof App. A.3, pp.44–45). Let `I` be a set of products with
uniform preference weights, `U` a vector with at most `C` units, and `U↑` a vector that agrees with
`U` outside `I` and satisfies the three properties of Lemma 6. Let `H` be a `(1 + ε)`-spaced subset
of `[C]` with `0` added, and `V^step_i = ⌊U↑_i⌋_H` for `i ∈ I`. Then
`U^step = (U↑ ↩_I V^step) = (U ↩_I V^step)` satisfies:
1. `E[X_i^{U^step}] ≥ E[X_i^U]` for every product `i ∉ I`;
2. `Σ_{i ∈ I} r_i E[X_i^{U^step}] ≥ (1 − ε)·Σ_{i ∈ I} r_i E[X_i^U]`;
3. `‖U^step‖₁ ≤ ‖U‖₁`. -/
theorem lemma_7 {n : ℕ} (wts : Weights n) (hw : wts.Pos) (r : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i)
    (pM : ℕ →₀ ℝ) (hM : IsLaw pM) (I : Finset (Fin n)) (hI : wts.UniformOn I) (C : ℕ)
    (U : Fin n → ℕ) (hU : norm1 U ≤ C) (Uup : Fin n → ℕ) (hoff : ∀ i, i ∉ I → Uup i = U i)
    (h1 : ∀ i, i ∉ I → expX wts pM Uup i = expX wts pM U i)
    (h2 : ∑ i ∈ I, r i * expX wts pM U i ≤ ∑ i ∈ I, r i * expX wts pM Uup i)
    (h3 : norm1 Uup = norm1 U) (ε : ℝ) (hε : 0 < ε) (H : Finset ℕ) (hH : IsSpaced ε C H) :
    (∀ i, i ∉ I → expX wts pM U i ≤ expX wts pM (swap I U fun i => floorH H (Uup i)) i) ∧
      (1 - ε) * ∑ i ∈ I, r i * expX wts pM U i ≤
        ∑ i ∈ I, r i * expX wts pM (swap I U fun i => floorH H (Uup i)) i ∧
      norm1 (swap I U fun i => floorH H (Uup i)) ≤ norm1 U := by sorry

end MNLStability
