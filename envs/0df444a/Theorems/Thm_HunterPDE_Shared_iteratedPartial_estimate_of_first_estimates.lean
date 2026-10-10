-- Prove2me | Theorems.Thm_HunterPDE_Shared_iteratedPartial_estimate_of_first_estimates
-- name    : HunterPDE.Shared.iteratedPartial_estimate_of_first_estimates
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-09T15:23:22.419747+00:00
-- url     : https://prove2.me/theorems/02e4beea-bf3d-4f54-ad73-444bf789ebfe
-- title:
--   Nested-ball propagation of coordinate derivative estimates
-- statement:
--   Let $\Omega\subseteq\mathbb R^n$, and let $u:\mathbb R^n\to\mathbb R$. Write $D_lu$ for the iterated coordinate derivative along a finite list $l$, with $D_{[]}u=u$ and $D_{i::l}u=\partial_i D_lu$. Suppose every $D_lu$ satisfies the following interior estimate: on every closed ball $\overline B_s(y)\subseteq\Omega$ with $s>0$, a bound $|D_lu|\le A$ implies $|\partial_iD_lu(y)|\le nA/s$ for every coordinate $i$. Then, for every list $l$ of length $k\ge1$, $r>0$, and $\overline B_r(x)\subseteq\Omega$ with $|u|\le M$ on that ball,
--
--   $$|D_lu(x)|\le\frac{n^ke^{k-1}k!}{r^k}M.$$
--
--   This abstracts the nested-ball induction behind harmonic interior estimates. It separates the geometric and numerical argument from the property that makes the first-derivative estimate available.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/ch2.pdf, pp. 21 and 23–24, Theorems 2.1–2.2 and proof of Theorem 2.9; generalized to constant directions / families satisfying first-derivative estimates.

import Definitions.Def_HunterPDE_Shared_PartialDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open HunterPDE.Shared Metric
set_option autoImplicit false

theorem HunterPDE.Shared.iteratedPartial_estimate_of_first_estimates {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hfirst : ∀ (l : List (Fin n)) (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      0 < r → closedBall x r ⊆ Ω → ∀ (i : Fin n) (M : ℝ),
      (∀ y ∈ closedBall x r, |iteratedPartial u l y| ≤ M) →
      |partialDeriv (iteratedPartial u l) i x| ≤ (n / r) * M)
    (l : List (Fin n)) (hl : 1 ≤ l.length)
    {x : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r)
    (hball : closedBall x r ⊆ Ω) {M : ℝ}
    (hM : ∀ y ∈ closedBall x r, |u y| ≤ M) :
    |iteratedPartial u l x| ≤
      ((n : ℝ) ^ l.length * Real.exp 1 ^ (l.length - 1) *
        (l.length.factorial : ℝ) / r ^ l.length) * M := by sorry
