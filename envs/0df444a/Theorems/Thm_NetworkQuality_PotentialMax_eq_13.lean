-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_eq_13
-- name    : NetworkQuality.PotentialMax.eq_13
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:04.768113+00:00
-- url     : https://prove2.me/theorems/cdd4fe94-8637-4ace-99a8-ec5c7df181f7
-- title:
--   (13), p. 14 — v₁f(1,q)Σ1/vᵢ ≤ Σf(i,q) ≤ vₙf(n,q)Σ1/vᵢ under strong network effects
-- statement:
--   In the network market under the standing assumptions, fix a quality $q\ge 0$ with strong network effects. Then
--   $$v_1f(1,q)\sum_{i=1}^n\frac1{v_i}\;\le\;\sum_{i=1}^n f(i,q)\;\le\;v_nf(n,q)\sum_{i=1}^n\frac1{v_i}.$$
--
--   Dividing by $\sum_i 1/v_i$, the threshold price $p(q)=\big(\frac1n\sum_i\frac1{v_i}\big)^{-1}\frac1n\sum_i f(i,q)$ of (12) satisfies $v_1f(1,q)\le p(q)\le v_nf(n,q)$: it lies in the price range in which both "all buy" and "none buy" are equilibria (Proposition 1(iii)).
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 14, (13)

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem eq_13 {n : ℕ} (M : Market n) (hM : M.Standing) (q : ℝ) (hq : 0 ≤ q)
    (hs : M.StrongNE q) :
    M.v ⟨0, hM.1⟩ * M.f 1 q * ∑ i : Fin n, 1 / M.v i ≤ ∑ i : Fin n, M.f (i.val + 1) q ∧
    ∑ i : Fin n, M.f (i.val + 1) q ≤
      M.v ⟨n - 1, Nat.sub_lt hM.1 Nat.one_pos⟩ * M.f n q * ∑ i : Fin n, 1 / M.v i := by sorry

end NetworkQuality.PotentialMax
