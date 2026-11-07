-- Prove2me | Theorems.Thm_KServerConj_lemma_1_2
-- name    : KServerConj.lemma_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:51:14.451096+00:00
-- url     : https://prove2.me/theorems/f929b899-839d-4f53-a7e2-9103e77d78c5
-- title:
--   Lemma 1.2 — duality: $\max_X\{w'(X)-w(X)\}=\min_Y\{w'(Y)-\sum_y d(r,y)\}-\min_Y\{w(Y)-\sum_y d(r,y)\}$
-- statement:
--   Let $M$ be a finite pseudometric space, $k\ge1$, $C_0$ a configuration of $k$ points, $r_1,r_2,\dots$ requests and $t\ge1$. Let $w=w_{t-1}$ be the work function before the request $r=r_t$ and $w'=w_t$ the work function after it. Then
--
--   $$\max_X\{w'(X)-w(X)\}=\min_Y\Big\{w'(Y)-\sum_{y\in Y}d(r,y)\Big\}-\min_Y\Big\{w(Y)-\sum_{y\in Y}d(r,y)\Big\},$$
--
--   where the maximum and both minima range over all configurations of $k$ points.
--
--   The extended cost of a request is thus the increase of the quantity $A_r(w)=\min_Y\{w(Y)-\sum_{y\in Y}d(r,y)\}$; the potential of the paper is built to combine these quantities for all $r$. This is the duality lemma of Koutsoupias and Papadimitriou, expressed in terms of minimum values.
--
--   Differences from the source:
--   - generalization: a metric space (M, d) → a pseudometric space (`PseudoMetricSpace M`); reason: the paper, p.1: "our proof works also when d is a pseudometric"; every metric space is a pseudometric space
--   - encoding: w a work function and w′ the work function after a request at r → w = w_{t−1} and w′ = w_t for some C₀, r and t ≥ 1, with r = r_t; reason: every work function is w_{t−1} for some initial configuration and request sequence
--   - encoding: k servers and a configuration C₀ → hypotheses 1 ≤ k and C₀.card = k; reason: configurations are k-element sets
--   - encoding: max and min over all configurations → iSup/iInf over the finite nonempty type of k-element subsets; reason: a supremum over a finite nonempty type is attained
-- source:
--   Coester, Koutsoupias, Zbysiński, The k-server conjecture is true, arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), Lemma 1.2, p.2 (pdf p.3)

import Mathlib
import Definitions.Def_KServerConj_extCost

namespace KServerConj

/-- **Lemma 1.2 (Duality).** Coester, Koutsoupias, Zbysiński, *The k-server conjecture is true*,
arXiv:2609.15979 (version of 2026-11-03, sha256 7ca0380a…), printed p.2 (PDF p.3): "Let w be a
work function and let w′ be the work function after a request at r. The extended cost is
max_X {w′(X) − w(X)} = min_Y {w′(Y) − ∑_{y∈Y} d(r, y)} − min_Y {w(Y) − ∑_{y∈Y} d(r, y)}, (4)
where the maximum and both minima range over all configurations."

**Formalization Note.** A work function is `w = w_{t−1}` for some initial configuration `C₀` of `k`
points and some request sequence `r`, and `w′ = w_t` is the work function after the request
`r = r_t`, for `t ≥ 1`. `M` is finite (standing assumption, printed p.1); the maximum is `extCost`
and the minima are infima over the finite nonempty type of `k`-point configurations. -/
theorem lemma_1_2 {M : Type*} [PseudoMetricSpace M] [Fintype M] (k : ℕ) (hk : 1 ≤ k)
    (C₀ : Finset M) (hC₀ : C₀.card = k) (r : ℕ → M) (t : ℕ) (ht : 1 ≤ t) :
    extCost k C₀ r t =
      (⨅ Y : {Y : Finset M // Y.card = k},
          (workFn k C₀ r t (Y : Finset M) - ∑ y ∈ (Y : Finset M), dist (r t) y)) -
      (⨅ Y : {Y : Finset M // Y.card = k},
          (workFn k C₀ r (t - 1) (Y : Finset M) - ∑ y ∈ (Y : Finset M), dist (r t) y)) := by sorry

end KServerConj
