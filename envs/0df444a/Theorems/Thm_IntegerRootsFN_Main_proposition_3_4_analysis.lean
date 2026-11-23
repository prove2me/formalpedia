-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_proposition_3_4_analysis
-- name    : IntegerRootsFN.Main.proposition_3_4_analysis
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:20:00.043857+00:00
-- url     : https://prove2.me/theorems/8d39bf33-692d-4239-b880-422994c989e8
-- title:
--   Proposition 3.4 — inverse transform and root-size correctness
-- statement:
--   Let $g\in\mathbb Z[x]$ satisfy the degree-$d$ and coefficient-height hypotheses of Proposition 3.4. Suppose $q$ is a Gaussian integer with $|q|\le10d^2+1$ whose distance from every root of $g$ is greater than $1$. Put $H=reverseShift(g,q)$, so $H(w)=w^dg(q+1/w)$, and let $P$ be the proposition's prescribed precision. If dyadic complex numbers $w_1,\ldots,w_d$ satisfy
--   $$
--   \left\|H-H_d\prod_{i=1}^d(X-w_i)\right\|_1\le2^{-P}\|H\|_1,
--   $$
--   then every $w_i$ is nonzero and the numbers $\beta_i=q+1/w_i$ satisfy both conclusions of Proposition 3.4: every root of $g$ lies at distance strictly less than $1/8$ from some $\beta_i$, and
--   $$
--   \sum_{i=1}^d\log_2\max(1,|\beta_i|)\le b+\frac12\log_2(d+1)+2.
--   $$
--
--   The proof applies the inverse transformation $E^*(x)=(x-q)^dE(1/(x-q))$, bounds its coefficient norm by $(10d^2+2)^d$, and uses the leading coefficient comparison to rule out $w_i=0$. The resulting polynomial has degree $d$ and complete root list $\beta_1,\ldots,\beta_d$, so Lemma 2.3 applies. This isolates the mathematical content of the second and third paragraphs of the proof on p.10; it does not assert any machine implementation or output-size bound.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 10, proof of Proposition 3.4, inverse transformation $E\mapsto E^*$, perturbation estimate, nonvanishing of $w_i$, and application of Lemma 2.3

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_Binary
import Definitions.Def_IntegerRootsFN_Main_ApproximationConstruction

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem proposition_3_4_analysis
    (d b : ℕ) (g : Polynomial ℤ) (hg : Valid g d b)
    (q : ℤ × ℤ) (B : ℕ) (ws : Fin d → ℤ × ℤ)
    (hq : ‖gaussianValue q‖ ≤ 10 * (d : ℝ) ^ 2 + 1)
    (hclear : ∀ α : ℂ, (complexify g).IsRoot α → 1 < ‖α - gaussianValue q‖)
    (hfactor : normOne (reverseShift g d q -
        factorPolynomial ((reverseShift g d q).coeff d)
          (fun i => ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B))) ≤
        (2 : ℝ) ^ (-(approximationPrecision d b : ℤ)) * normOne (reverseShift g d q)) :
    (∀ i, ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B) ≠ 0) ∧
    CoversRoots (complexify g)
      (fun i => gaussianValue q + 1 / ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B)) ∧
    logRootSize
      (fun i => gaussianValue q + 1 / ApproxGKR.dyadicVal ((ws i).1, (ws i).2, B)) ≤
      rootSizeBound d b := by sorry
