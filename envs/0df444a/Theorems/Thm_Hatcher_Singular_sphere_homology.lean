-- Prove2me | Theorems.Thm_Hatcher_Singular_sphere_homology
-- name    : Hatcher.Singular.sphere_homology
-- status  : Proved
-- author  : @Idealson
-- created : 2026-10-21T08:27:22.879048+00:00
-- url     : https://prove2.me/theorems/1469d638-9e7e-4d9f-a27c-fd515e7ce38f
-- title:
--   Homology of spheres: $H_k(S^n;R)\cong R$ for $k=0,n$ and $0$ otherwise
-- statement:
--   Let $R$ be a ring, $n\ge 0$, and let $S^n=\{x\in\mathbb R^{n+1}:\ \|x\|=1\}$ be the unit sphere of Euclidean space $\mathbb R^{n+1}$. Then:
--
--   1. $H_k(S^n;R)=0$ for every $k\ne 0,n$;
--   2. if $n\ge 1$, $H_n(S^n;R)\cong R$;
--   3. if $n\ge 1$, $H_0(S^n;R)\cong R$.
--
--   For $n=0$ the sphere $S^0$ consists of two points and $H_0(S^0;R)\cong R^2$; this case is excluded from items 2 and 3 (item 1 still holds).
--
--   This computation underlies degree theory, the Brouwer fixed point theorem and the cellular homology of CW complexes.
--
--   **Formalization Note** $S^n$ is `Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1` with the subspace topology; vanishing is stated as `IsZero` in the category of $R$-modules, and the isomorphisms are isomorphisms of $R$-modules with $R$.
-- source:
--   A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002 (online edition: https://pi.math.cornell.edu/~hatcher/AT/AT.pdf), §2.1, Corollary 2.14 (p. 114, reduced homology $\tilde H_i(S^n)$ with integer coefficients) and Proposition 2.7 (p. 109) for $H_0$; arbitrary coefficients as in §2.2 (p. 153). Lean: original formalization for this project (Lean v4.33.1, Mathlib 0df444a), file `Bridge/Singular/Spheres.lean`.

import Mathlib
import Definitions.Def_Hatcher_SingularHomology

open CategoryTheory Limits

theorem Hatcher.Singular.sphere_homology (R : Type) [Ring R] (n : ℕ) :
    (∀ k : ℕ, k ≠ 0 → k ≠ n →
      IsZero (H R k (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))) ∧
    (n ≠ 0 → Nonempty
      (H R n (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≅ ModuleCat.of R R)) ∧
    (n ≠ 0 → Nonempty
      (H R 0 (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) ≅ ModuleCat.of R R)) := by sorry
