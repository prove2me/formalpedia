-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation
-- name    : HunterPDE.Sobolev.smooth_compact_cutoff_approximation
-- status  : Open
-- author  : @Mazecto
-- created : 2026-10-10T22:16:52.500591+00:00
-- url     : https://prove2.me/theorems/019940cc-0bac-4576-a96f-999dd4b0a81b
-- title:
--   Compact cutoff approximation of smooth Sobolev functions
-- statement:
--   Let $k\ge0$, $1\le p<\infty$, and let $g\in C^\infty(\mathbb R^n)\cap W^{k,p}(\mathbb R^n)$. For every positive tolerance there is a smooth compactly supported function $\varphi$ belonging to $W^{k,p}(\mathbb R^n)$ such that
--
--   $$\|g-\varphi\|_{W^{k,p}(\mathbb R^n)}<\varepsilon.$$
--
--   This is the second step of Hunter's proof of Theorem 3.24. Multiply $g$ by a smooth cutoff equal to one on the ball of radius $R$ and supported in the ball of radius $2R$. The Leibniz rule, decay of derivatives of the rescaled cutoff, and dominated convergence give approximation as $R\to\infty$. The statement includes order zero and explicitly records Sobolev membership of the approximant for downstream norm estimates.
-- source:
--   John K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 58–60, Definition 3.23 and proof of Theorem 3.24.

import Definitions.Def_HunterPDE_Sobolev_SobolevSpace

open MeasureTheory
open HunterPDE.Sobolev

theorem HunterPDE.Sobolev.smooth_compact_cutoff_approximation {n k : ℕ}
    {p : ENNReal} (hp : 1 ≤ p) (hptop : p ≠ ⊤)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g) (hgW : MemW k p Set.univ g)
    (ε : ENNReal) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin n) → ℝ,
      IsTestFunction Set.univ φ ∧ MemW k p Set.univ φ ∧
        sobolevNorm k p Set.univ (g - φ) < ε := by sorry
