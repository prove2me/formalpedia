-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation_support
-- name    : HunterPDE.Sobolev.smooth_compact_cutoff_approximation_support
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T21:03:24.631645+00:00
-- url     : https://prove2.me/theorems/2a30723c-6954-4b25-85a0-ad76a62a00bc
-- title:
--   Compact Sobolev cutoff approximation preserving topological support
-- statement:
--   For every globally smooth function $g$ in $W^{k,p}(\mathbb R^n)$, where $k\ge0$ and $1\le p<\infty$, and every positive extended-real error $\varepsilon$, there is $\varphi\in C_c^\infty(\mathbb R^n)\cap W^{k,p}(\mathbb R^n)$ such that
--
--   $$\|g-\varphi\|_{W^{k,p}(\mathbb R^n)}<\varepsilon,\qquad \operatorname{supp}\varphi\subseteq\operatorname{supp}g.$$
--
--   Here support denotes closed topological support. Multiplication by expanding compact cutoffs therefore preserves any prescribed support containment.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorem 3.24, printed pp. 58–59 (large-radius cutoff); support-preserving refinement used in the argument following Theorem 3.44 on printed p. 73.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory
open HunterPDE.Sobolev
set_option autoImplicit false

theorem HunterPDE.Sobolev.smooth_compact_cutoff_approximation_support {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgW : MemW k p Set.univ g)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsTestFunction Set.univ φ ∧ MemW k p Set.univ φ ∧
        sobolevNorm k p Set.univ (g - φ) < ε ∧ tsupport φ ⊆ tsupport g := by sorry
