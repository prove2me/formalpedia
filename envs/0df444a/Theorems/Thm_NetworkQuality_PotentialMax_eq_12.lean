-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_eq_12
-- name    : NetworkQuality.PotentialMax.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:03.022992+00:00
-- url     : https://prove2.me/theorems/9784aa71-1049-4bcf-a10e-201bca8fa712
-- title:
--   (12), p. 14 — under strong network effects the potential maximizer is N iff p ≤ harmonic mean × uniform expectation
-- statement:
--   In the network market under the standing assumptions, fix a quality $q\ge 0$ with strong network effects and a price $p$. Then
--   1. every maximizer of $\Phi(\cdot,p,q)$ over all buyer sets is either $N$ or $\emptyset$; and
--   2. $N$ is a potential maximizer if and only if
--   $$p\le\Big(\frac1n\sum_{i=1}^n\frac1{v_i}\Big)^{-1}\,\frac1n\sum_{i=1}^n f(i,q).$$
--
--   The right-hand side is the harmonic mean of the valuations times the "uniform expectation" of the benefit, i.e. the expected benefit when the number of buyers is uniform on $\{1,\dots,n\}$. This is the price $p(q)$ up to which a firm anticipating potential maximization sells to everybody.
--
--   **Formalization Note** The paper derives (12) by comparing $\Phi(N,p,q)$ with $\Phi(\emptyset,p,q)=0$ in the region where both are equilibria; here it is stated for every price $p$, which holds because outside that region the unique equilibrium is the one (12) predicts. Potential maximizers range over all subsets of $N$.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 14, (12)

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem eq_12 {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) (p : ℝ) :
    (∀ B : Finset (Fin n), M.IsPotMax B p q → B = Finset.univ ∨ B = ∅) ∧
    (M.IsPotMax Finset.univ p q ↔
      p ≤ ((1 / (n : ℝ)) * ∑ i : Fin n, 1 / M.v i)⁻¹ *
        ((1 / (n : ℝ)) * ∑ i : Fin n, M.f (i.val + 1) q)) := by sorry

end NetworkQuality.PotentialMax
