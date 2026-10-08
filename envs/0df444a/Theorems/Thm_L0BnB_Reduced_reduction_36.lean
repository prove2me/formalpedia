-- Prove2me | Theorems.Thm_L0BnB_Reduced_reduction_36
-- name    : L0BnB.Reduced.reduction_36
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:13:52.065779+00:00
-- url     : https://prove2.me/theorems/96baa931-d55d-4e28-b899-798430061d90
-- title:
--   Proof of Theorem 1 — reduction of the coordinate problem ω to the one-variable problem (36)
-- statement:
--   Fix $\lambda_0,\lambda_2,M>0$ and $b\in\mathbb R$ with $|b|\le M$. Consider the one-coordinate constraints of the interval relaxation of the perspective formulation,
--   $$b^2\le sz,\qquad -Mz\le b\le Mz,\qquad 0\le z\le 1,\qquad s\ge 0,$$
--   and let $\hat z=\max\{b^2/s,\,|b|/M\}$, with $b^2/s:=0$ when $b=s=0$. Then:
--
--   1. every feasible pair $(z,s)$ satisfies $s\ge b^2$ and $z\ge\hat z$;
--   2. for every $s\ge b^2$, the pair $(\hat z,s)$ is feasible;
--   3. consequently, a real number $v$ is the minimum of $\lambda_0 z+\lambda_2 s$ over the feasible pairs if and only if it is the minimum of problem (36),
--   $$
--   \omega(b;\lambda_0,\lambda_2,M)=\min_{s}\ \max\Big\{\lambda_0\frac{b^2}{s}+\lambda_2 s,\ \lambda_0\frac{|b|}{M}+\lambda_2 s\Big\}\quad\text{s.t.}\quad s\ge b^2 .
--   $$
--
--   This eliminates the indicator variable $z$ and turns the computation of $\omega$ into a one-dimensional minimization over $s$, which the two cases of the proof of Theorem 1 then solve.
--
--   **Formalization Note** "Is the minimum" is `IsLeast`: the value belongs to the set and bounds it from below. The paper's side condition $|\beta_i|\le M$ of (36) is the hypothesis on $b$.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 28, App. A, Proof of Theorem 1, reduction to (36)

import Mathlib
import Definitions.Def_L0BnB_Reduced_ReverseHuber
import Definitions.Def_L0BnB_Reduced_Setup

namespace L0BnB.Reduced

/-- Proof of Theorem 1, p. 28: for one coordinate `b` with `|b| ≤ M`, every feasible `(z, s)` of
(35b)–(35d) has `s ≥ b²` and `z ≥ ẑ = max{b²/s, |b|/M}`; for every `s ≥ b²` the pair `(ẑ, s)` is
feasible; hence `ω(b; λ₀, λ₂, M)` is the minimum of (36). -/
theorem reduction_36 (lam0 lam2 M b : ℝ) (h0 : 0 < lam0) (h2 : 0 < lam2) (hM : 0 < M)
    (hb : |b| ≤ M) :
    (∀ z s : ℝ, CoordFeas M b z s → b ^ 2 ≤ s ∧ zhat M b s ≤ z) ∧
    (∀ s : ℝ, b ^ 2 ≤ s → CoordFeas M b (zhat M b s) s) ∧
    (∀ v : ℝ, IsLeast (omegaValues lam0 lam2 M b) v ↔ IsLeast (values36 lam0 lam2 M b) v) := by sorry

end L0BnB.Reduced
