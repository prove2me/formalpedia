-- Prove2me | Theorems.Thm_LiuHelsenDesigns_OneD_lemma_7
-- name    : LiuHelsenDesigns.OneD.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T11:09:31.101495+00:00
-- url     : https://prove2.me/theorems/c78c7c17-fcbe-4ab3-89d1-60cb8db11639
-- title:
--   Lemma 7 — diagonal and off-diagonal row bounds
-- statement:
--   Let $k\le\xi-1$ and put $\eta=\|(2^{\xi k}Wg_C)^{-1}-I\|_{\infty\to\infty}$. For every stochastic Lagrangian T,
--
--   $$
--   \eta\le2^{k-\xi},\qquad 2^{\xi k}|Wg_C(T,T)|\le\frac1{1-\eta},\qquad\sum_{S\ne T}2^{\xi k}|Wg_C(T,S)|\le\frac\eta{1-\eta}.
--   $$
--
--   Both absolute-value bounds are retained and use the computed row norm.
--
--   Differences from the source: none.
-- source:
--   Guoding Liu, Jonas Helsen, STOC 2027 submission #221 (October 2026), p. 18, Lemma 7. https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/221.pdf

import Definitions.Def_LiuHelsenDesigns_OneD_commutants

namespace LiuHelsenDesigns.OneD
theorem lemma_7 (ξ k : ℕ) (hrange : k + 1 ≤ ξ) :
    eta ξ k ≤ (2 : ℝ)^((k : ℤ)-ξ) ∧
    ∀ T : Sigma k,
      (2 : ℝ)^(ξ*k) * |wgC ξ k T T| ≤ 1 / (1-eta ξ k) ∧
      (∑ S : Sigma k, if S ≠ T then (2 : ℝ)^(ξ*k) * |wgC ξ k T S| else 0) ≤
        eta ξ k / (1-eta ξ k) := by sorry
end LiuHelsenDesigns.OneD
