-- Prove2me | Theorems.Thm_GroupBuyEq_Signup_H_boundary
-- name    : GroupBuyEq.Signup.H_boundary
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T09:20:37.549705+00:00
-- url     : https://prove2.me/theorems/613deb49-2963-4141-9407-cc9a1e0f0b0a
-- title:
--   §3.2, p. 9 — boundary condition H_k(t) = 1 − F(p₂) for k ≥ M₂ − 1
-- statement:
--   In the two-threshold group-buying model under the standing assumptions, let $\mu$ be a probability law on $\mathbb R$ without atoms for the reservation utility, with c.d.f. $F$, and let $(\pi^1_k,\pi^2_k)_{k\ge0}$ be a dynamic consumer equilibrium. Then for every $k\ge M_2-1$ and $t\in[0,T]$,
--   $$H_k(t)=1-F(p_2).$$
--
--   A customer who sees $k\ge M_2-1$ sign-ups secures the second deal by joining, so he signs up exactly when $u\ge p_2$. This boundary condition starts the backward induction over $k$ in the proof of Proposition 1.
--
--   **Formalization Note** "$k\ge M_2-1$" is written $M_2\le k+1$, avoiding natural-number subtraction. The proof of Proposition 1 uses the weaker version for $k\ge M_2$; the statement is the one printed on p. 9. No atoms (rather than a density) is assumed for $\mu$.
-- source:
--   Ming & Tunca, Consumer Equilibrium, Demand Effects, and Efficiency in Group Buying, SSRN 3352047 (version of 2020-05-15), p. 9 (PDF 10), §3.2

import Mathlib
import Definitions.Def_GroupBuyEq_Signup_Model

namespace GroupBuyEq.Signup

theorem H_boundary (P : Params) (hP : P.Standing) (μ : MeasureTheory.Measure ℝ)
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.NullSingletonClass μ] (E : Profile)
    (hE : IsEquilibrium P μ E) (k : ℕ) (hk : P.M2 ≤ k + 1) (t : ℝ) (ht : t ∈ Set.Icc 0 P.T) :
    H P μ E k t = 1 - ProbabilityTheory.cdf μ P.p2 := by sorry

end GroupBuyEq.Signup
