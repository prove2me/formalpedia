-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_eq_7
-- name    : GroupBuyEq.Signup.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:34.631209+00:00
-- url     : https://prove2.me/theorems/4d1fc8b0-3730-47c3-9520-cf7dfb4600f4
-- title:
--   Proof of Proposition 1, p. A.3 — (7): Pr{V ≥ 0} = 1 − F(ū), by Lemma 1
-- statement:
--   In the two-threshold group-buying model with deposit $d>0$ and discount $\delta\ge0$, let $a,b\ge0$ with $a+b\le1$, let $\mu$ be a probability law on $\mathbb R$ without atoms for the reservation utility, and let $F$ be its cumulative distribution function. Then
--   $$\mu\{u:\ V(a,b,u)\ge0\}=1-F(\bar u(a,b)),$$
--   where $V$ is the expected utility (1) of signing up and $\bar u$ the threshold (3).
--
--   Applied to $a=\pi^1_{k+1}(t)$, $b=\pi^2_{k+1}(t)$ this is equation (7), $H_k(t)=1-F(\bar u_{k,t})$: the sign-up probability (2) in closed form. It is the step that turns the conditioning equations into an explicit recursion in Proposition 1.
--
--   **Formalization Note** The paper assumes that $F$ has a density; the statement assumes only that $\mu$ has no atoms (`NullSingletonClass`), which is weaker and is what the identity needs. $F$ is Mathlib's `ProbabilityTheory.cdf μ`, $F(x)=\mu(-\infty,x]$.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), p. A.3 (PDF 36), proof of Proposition 1; equation (7), p. 11 (PDF 12)

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem eq_7 (P : Params) (hd : 0 < P.d) (hδ : 0 ≤ P.δ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 1) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ] :
    (μ {u | 0 ≤ V P a b u}).toReal = 1 - ProbabilityTheory.cdf μ (ubar P a b) := by sorry

end GroupBuyEq.Signup
