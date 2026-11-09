-- Prove2me | Theorems.Thm_MultiSpinCounting_Positive_lemma_3_2
-- name    : MultiSpinCounting.Positive.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:17:29.132466+00:00
-- url     : https://prove2.me/theorems/e7c82b6c-6d05-45b2-ab21-5f6f2ba3f989
-- title:
--   Lemma 3.2 — marginal-ratio recursion
-- statement:
--   Let $\Phi$ be a positive real multi-spin instance, let $v$ be active, and order its neighbors as $v_1,\ldots,v_d$. For spins $a,b$, let $\Phi_i$ be the child instance of Definition 3.1. Then
--   $$\frac{\mu_\Phi(v\leftarrow a)}{\mu_\Phi(v\leftarrow b)}=\frac{\lambda_v(a)}{\lambda_v(b)}\prod_{i=1}^d\frac{\sum_k A_{v,v_i}(a,k)\mu_{\Phi_i}(v_i\leftarrow k)}{\sum_k A_{v,v_i}(b,k)\mu_{\Phi_i}(v_i\leftarrow k)}.$$
--   The identity retains positive real interactions and fields; rationality is unnecessary here. It relates the parent marginal ratio to actual child Gibbs marginals.
--
--   Differences from the source:
--   - encoding: finite ordered vertex and spin sets → Fin n and Fin q, with an active vertex subset; reason: relabeling preserves every instance; active subsets implement the source sub-instances and the fixed vertex order
--   - generalization: the multi-spin setting of the paper → every nonempty finite spin set, including one or two spins; reason: the same identity holds and specializes to the paper’s q ≥ 3 setting
-- source:
--   Zhidan Li, Kuan Yang, STOC 2027 submission #268 (October 2026), p. 11, Lemma 3.2 and Definition 3.1

import Mathlib
import Definitions.Def_MultiSpinCounting_Positive_Instance

namespace MultiSpinCounting.Positive

/-- Lemma 3.2, p. 11, over positive real inputs (not just rational inputs). -/
theorem lemma_3_2 {n q : ℕ} (hq : 0 < q) (Φ : Instance n q ℝ)
    (hΦ : IsPositive Φ) (v : Fin n) (hv : v ∈ Φ.active) (a b : Fin q) :
    marginal Φ v a / marginal Φ v b = Φ.field v a / Φ.field v b *
      ∏ i ∈ neighbors Φ v,
        (∑ k, Φ.interaction v i a k * marginal (child Φ v i a b) i k) /
        (∑ k, Φ.interaction v i b k * marginal (child Φ v i a b) i k) := by sorry

end MultiSpinCounting.Positive
