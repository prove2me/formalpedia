-- Prove2me | Theorems.Thm_OfflineStochMatch_UnitPatience_eq_29
-- name    : OfflineStochMatch.UnitPatience.eq_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:12:25.498757+00:00
-- url     : https://prove2.me/theorems/e6bbd689-baae-4141-8808-8de191955cc9
-- title:
--   Eq. (29), p. 18 — F(i) ≥ 1 − e^{−F*(i)} ≥ (1 − 1/e)F*(i) when z_j ∈ [0,1] and Σ_{j≤k} z_j ≤ 1
-- statement:
--   Let $z_1,\dots,z_k\in[0,1]$ with $\sum_{j=1}^{k}z_j\le 1$, and for $0\le i\le k$ put $F(i)=1-\prod_{j=1}^{i}(1-z_j)$ and $F^*(i)=\sum_{j=1}^{i}z_j$. Then
--   $$F(i)\ \ge\ 1-e^{-F^*(i)}\ \ge\ \Big(1-\frac1e\Big)F^*(i).\tag{29}$$
--
--   The first inequality is the bound $\prod_{j=1}^{i}(1-z_j)\le e^{-F^*(i)}$, which the page derives from the inequality of arithmetic and geometric means; the second uses $0\le F^*(i)\le\sum_{j=1}^{k}z_j\le 1$. Together with (27) and (28) it gives Lemma 8.
--
--   **Formalization Note** The two inequalities are stated as a conjunction; $1-1/e$ is written $1-e^{-1}$. The sequence is indexed by $\mathbb N$ and only the indices $1,\dots,k$ are constrained.
-- source:
--   Brubach, Grammel, Ma, MacRury, Srinivasan, Improved Guarantees for Offline Stochastic Matching via New Ordered Contention Resolution Schemes, arXiv:2106.06892v3, p. 18, Eq. (29) (proof of Lemma 8; F(i) defined on p. 17, F*(i) on p. 18)

import Mathlib
import Definitions.Def_OfflineStochMatch_UnitPatience_Setting

namespace OfflineStochMatch.UnitPatience

open Finset

theorem eq_29 (k : ℕ) (z : ℕ → ℝ) (hz : ∀ j ∈ Icc 1 k, 0 ≤ z j ∧ z j ≤ 1)
    (hsum : ∑ j ∈ Icc 1 k, z j ≤ 1) (i : ℕ) (hi : i ≤ k) :
    1 - Real.exp (-Fstar z i) ≤ Fcum z i ∧
    (1 - Real.exp (-1)) * Fstar z i ≤ 1 - Real.exp (-Fstar z i) := by sorry

end OfflineStochMatch.UnitPatience
