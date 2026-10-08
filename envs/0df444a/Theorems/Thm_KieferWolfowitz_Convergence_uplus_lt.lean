-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_uplus_lt
-- name    : KieferWolfowitz.Convergence.uplus_lt
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:18.146245+00:00
-- url     : https://prove2.me/theorems/580ed974-0448-4890-8c2c-b6daac2cbcad
-- title:
--   (3.8), p. 464 — $0\le U_n^+(z)<2Bc_n^2$ whenever $c_n<\tfrac12\beta$
-- statement:
--   Let $M:\mathbb R\to\mathbb R$ be strictly increasing on $\{x<\theta\}$ and strictly decreasing on $\{x>\theta\}$, and let $M$ satisfy Condition 1 with constants $\beta,B>0$: $|M(x')-M(x'')|<B|x'-x''|$ whenever $x'\neq x''$ and $|x'-\theta|+|x''-\theta|<\beta$. For $c>0$ and $z\in\mathbb R$ put
--   $$U(z)=(z-\theta)\big(M(z+c)-M(z-c)\big),\qquad U^+(z)=\max(U(z),0).$$
--   Then for every $z$ and every $0<c<\tfrac12\beta$,
--   $$0\le U^+(z)<2Bc^2.$$
--
--   With $c=c_n$ this is the paper's (3.8), $0\le U_n^+(z)<2Bc_n^2$ for all $n$ with $c_n<\frac12\beta$. It is a deterministic statement: it bounds the only term of the one-step identity (3.6) that can increase the mean squared error, and combined with $\sum a_nc_n<\infty$ it makes the positive-term series $\sum (a_n/c_n)P_n$ converge.
--
--   **Formalization Note** The statement is about a real number $c$ in place of $c_n$; the probabilistic model plays no role. Condition 1 carries the added hypothesis $x'\neq x''$ (see the model definition).
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 464, (3.8)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.8), p. 464: if `M` is strictly increasing left of `θ`, strictly
decreasing right of `θ` and satisfies Condition 1 with constants `β, B`, then
`0 ≤ U⁺(z) < 2 B c²` for every `z` and every `0 < c < β/2`. -/
theorem uplus_lt (M : ℝ → ℝ) (θ β B : ℝ) (hβ : 0 < β) (hB : 0 < B)
    (hM : Unimodal M θ) (h1 : Cond1 M θ β B) (c z : ℝ) (hc : 0 < c) (hcβ : c < β / 2) :
    0 ≤ Uplus M θ c z ∧ Uplus M θ c z < 2 * B * c ^ 2 := by sorry

end KieferWolfowitz.Convergence
