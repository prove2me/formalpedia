-- Prove2me | Theorems.Thm_OptStochMatch_Tight_lemma_4_3
-- name    : OptStochMatch.Tight.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T02:55:10.794383+00:00
-- url     : https://prove2.me/theorems/01788f17-1497-4bf1-a288-b7a5fe76c75c
-- title:
--   Lemma 4.3 — PDE for q and the sensitivity bound (4.6)
-- statement:
--   For $0\le t\le1$ and $h\ge0$, $q$ satisfies $\partial_tq(t,h)+(h+1)\big(1+\partial_hq(t,h)-q(t,h)\big)=0$ (4.5), and consequently $0\le1+\partial_hq(t,h)-q(t,h)\le-\partial_tq(t,0)$ (4.6).
--
--   Differences from the source:
--   - reading: the partial derivatives ∂_t q, ∂_h q on 0 ≤ t ≤ 1, h ≥ 0 → two-sided derivatives (`deriv`) of q in t and in h, whose existence is asserted; reason: the PDE presupposes the derivatives; q is defined for all real t, h and is differentiable at the boundary points t ∈ {0, 1}, h = 0, so the two-sided derivative is the source's
-- source:
--   Dütting, Feldman, Molina, Optimal Online Stochastic Matching, arXiv:2610.19866 (sha256 0458ce2e…), Lemma 4.3, eqs. (4.5)–(4.6), p. 15 (PDF p. 16)

import Mathlib
import Definitions.Def_OptStochMatch_Tight_Comparison

namespace OptStochMatch.Tight

/-- Lemma 4.3 (p. 15, PDF 16). For `0 ≤ t ≤ 1` and `h ≥ 0`, `q` is differentiable in `t` and in
`h` and satisfies the PDE `∂_t q(t,h) + (h + 1)(1 + ∂_h q(t,h) − q(t,h)) = 0` (4.5); as a
consequence `0 ≤ 1 + ∂_h q(t,h) − q(t,h) ≤ −∂_t q(t, 0)` (4.6). -/
theorem lemma_4_3 (t h : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hh : 0 ≤ h) :
    DifferentiableAt ℝ (fun t' => qComp t' h) t ∧
    DifferentiableAt ℝ (fun h' => qComp t h') h ∧
    DifferentiableAt ℝ (fun t' => qComp t' 0) t ∧
    deriv (fun t' => qComp t' h) t +
        (h + 1) * (1 + deriv (fun h' => qComp t h') h - qComp t h) = 0 ∧
    0 ≤ 1 + deriv (fun h' => qComp t h') h - qComp t h ∧
    1 + deriv (fun h' => qComp t h') h - qComp t h ≤ -deriv (fun t' => qComp t' 0) t := by sorry

end OptStochMatch.Tight
