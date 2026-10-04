-- Prove2me | Theorems.Thm_MulticlassQNet_SingleStation_proof_8_3_extreme_points
-- name    : MulticlassQNet.SingleStation.proof_8_3_extreme_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T08:12:55.626018+00:00
-- url     : https://prove2.me/theorems/08ff25d8-f255-4fbf-8f98-d60e42d9dcb0
-- title:
--   Proof of Theorem 8.3 — the extreme points of P1 are the n! vectors v(π), and P1 is their convex hull
-- statement:
--   Consider the multiclass single-server queue with classes $E=\{1,\dots,n\}$, arrival rates $\lambda_i>0$, service rates $\mu_i>0$ and load $\sum_{i\in E}\lambda_i/\mu_i<1$. Let $\mathrm{P1}\subseteq\mathbb R_+^n$ be the polyhedron of Theorem 8.3,
--   $$
--   \sum_{i\in S}\frac{n_i}{\mu_i}\ \ge\ \frac{\sum_{i\in S}\rho_i/\mu_i}{1-\sum_{i\in S}\rho_i}\quad(S\subset E),\qquad \sum_{i\in E}\frac{n_i}{\mu_i}=\frac{\sum_{i\in E}\rho_i/\mu_i}{1-\sum_{i\in E}\rho_i},
--   $$
--   with $\rho_i=\lambda_i/\mu_i$, and for each permutation $\pi$ of $E$ let $v(\pi)$ be the solution of the system (58), $\sum_{j\le k}x_{\pi_j}/\mu_{\pi_j}=b(\{\pi_1,\dots,\pi_k\})$ for $k=1,\dots,n$. Then
--
--   1. the extreme points of P1 are exactly the vectors $v(\pi)$, $\pi$ ranging over the $n!$ permutations of $E$;
--   2. P1 is the convex hull of these vectors:
--   $$
--   \operatorname{ext}\mathrm{P1}=\{v(\pi):\pi\in\mathfrak S_E\},\qquad \mathrm{P1}=\operatorname{conv}\{v(\pi):\pi\in\mathfrak S_E\}.
--   $$
--
--   This is the polyhedral content of the paper's argument that P1 is an (extended) polymatroid base: it identifies the vertices with the performance vectors of the $n!$ preemptive priority rules and makes linear optimization over P1 a greedy computation (the $c\mu$ rule).
--
--   **Formalization Note** The statement concerns only the explicit vectors $v(\pi)$; the paper's further claims that $v(\pi)$ is the performance of a priority rule and that P1 is the achievable region are not formalized (no policy appears). "Having $n!$ extreme points" is stated as the equality of the extreme-point set with the range of $\pi\mapsto v(\pi)$, without a cardinality claim (different permutations could in principle give equal vectors). Conventions are those of the definition `MulticlassQNet.SingleStation.Polyhedra`.
-- source:
--   Bertsimas, Paschalidis, Tsitsiklis, Optimization of Multiclass Queueing Networks: Polyhedral and Nonlinear Characterizations of Achievable Performance, MIT Sloan WP #3509-92-MSA (Dec. 1992), p. 37, §8.2, proof of Theorem 8.3, third paragraph; Eq. (58) p. 33

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra

namespace MulticlassQNet.SingleStation

/-- Proof of Theorem 8.3 (p. 37): P1 is an (extended) polymatroid base whose extreme points are
exactly the vectors `v(π)` of (58), one per permutation `π` of the classes, and every point of P1
is a convex combination of them. -/
theorem proof_8_3_extreme_points {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    Set.extremePoints ℝ (P1 lam mu) = Set.range (v lam mu) ∧
      P1 lam mu = convexHull ℝ (Set.range (v lam mu)) := by sorry

end MulticlassQNet.SingleStation
