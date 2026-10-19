-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_weak_morrey_representative
-- name    : HunterPDE.Sobolev.weak_morrey_representative
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:03:15.47679+00:00
-- url     : https://prove2.me/theorems/786bedb8-e687-4d6e-800a-09794ca50991
-- title:
--   Global Morrey representative estimate for weak gradients in Lp, p > n
-- statement:
--   Let $n\ge1$ and $n<p<\infty$. There is a constant $A=A(n,p)\ge0$ such that every real function $f$ on $\mathbb R^n$ with weak first partial derivatives in $L^p$ and gradient bound $\|Df\|_p\le C$ has a continuous representative $u=f$ almost everywhere satisfying
--   $$|u(x)-u(y)|\le AC|x-y|^{1-n/p}\qquad(x,y\in\mathbb R^n).$$
--   The same constant works for all functions and all finite nonnegative bounds $C$. No integrability or decay of $f$ at infinity is required; constants are allowed. Local integrability is included in the weak derivative predicate, and positive dimension ensures at least one such predicate is assumed.
--
--   This is the homogeneous weak-function version of Morrey's increment estimate, useful for compact embedding and local regularity. It extracts the representative and increment estimate used in the proof of Hunter's Theorem 3.37; the additional global $L^p$ assumption there is used for boundedness and vanishing at infinity, which are not conclusions of this statement.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, pp. 68–70, Theorem 3.36 Eq. (3.12) and the representative/increment argument in the proof of Theorem 3.37 (homogeneous formulation, without its decay conclusion)

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

open MeasureTheory
open scoped ENNReal NNReal

theorem HunterPDE.Sobolev.weak_morrey_representative {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ) (hnp : (n : ℝ) < p) :
    ∃ A : ℝ≥0, ∀ f : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
        HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧
          MemLp g (ENNReal.ofReal p) volume) →
      ∀ C : ℝ≥0,
        eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤
          (C : ℝ≥0∞) →
      ∃ u : EuclideanSpace ℝ (Fin n) → ℝ, Continuous u ∧ u =ᵐ[volume] f ∧
        ∀ x y, dist (u x) (u y) ≤ (A : ℝ) * (C : ℝ) *
          dist x y ^ (1 - (n : ℝ) / p) := by sorry
