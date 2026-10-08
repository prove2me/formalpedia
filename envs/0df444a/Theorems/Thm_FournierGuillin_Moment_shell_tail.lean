-- Prove2me | Theorems.Thm_FournierGuillin_Moment_shell_tail
-- name    : FournierGuillin.Moment.shell_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:23:17.607929+00:00
-- url     : https://prove2.me/theorems/a0624c8c-7b5f-42ac-9ad8-d630b15e0b54
-- title:
--   Proof of Theorem 1, p. 8 — M_q(μ) = 1 implies μ(B_n) ≤ 2^{−q(n−1)} for all n ≥ 0
-- statement:
--   Let $d\ge1$, $q>0$, and let $\mu$ be a probability measure on $\mathbb R^d$ with $M_q(\mu)=\int|x|^q\,\mu(dx)=1$. Then for every $n\ge0$,
--   $$\mu(B_n)\le 2^{-q(n-1)},$$
--   where $B_0=(-1,1]^d$ and $B_n=(-2^n,2^n]^d\setminus(-2^{n-1},2^{n-1}]^d$ for $n\ge1$.
--
--   This tail estimate for the dyadic shells is the only way the moment condition enters the proof of Theorem 1, after the scaling reduction to $M_q(\mu)=1$.
-- source:
--   Fournier & Guillin, arXiv:1312.2128v1, Proof of Theorem 1, p. 8, second sentence

import Mathlib
import Definitions.Def_WassersteinLinOpt_Ball_wassersteinDist
import Definitions.Def_WassersteinDRO_Duality_empiricalDistribution
import Definitions.Def_FournierGuillin_Moment_Setting

open MeasureTheory
open scoped ENNReal

namespace FournierGuillin.Moment

/-- Proof of Theorem 1, p. 8, second sentence: if `M_q(μ) = 1` then `μ(B_n) ≤ 2^{−q(n−1)}` for all
`n ≥ 0`. -/
theorem shell_tail {d : ℕ} (hd : 1 ≤ d) {q : ℝ} (hq : 0 < q)
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ] (hμ : moment q μ = 1) :
    ∀ n : ℕ, μ (shell n) ≤ ENNReal.ofReal (2 ^ (-(q * ((n : ℝ) - 1)))) := by sorry

end FournierGuillin.Moment
