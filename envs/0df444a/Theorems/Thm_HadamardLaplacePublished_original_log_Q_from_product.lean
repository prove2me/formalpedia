-- Prove2me | Theorems.Thm_HadamardLaplacePublished_original_log_Q_from_product
-- name    : HadamardLaplacePublished.original_log_Q_from_product
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:08:44.909535+00:00
-- url     : https://prove2.me/theorems/209c2654-5883-43c0-a744-baea104693ee
-- title:
--   From a normalized Hadamard identity to the integral of the original logarithmic Q
-- statement:
--   Let \(\Re B_j\ge1\) and \(\sum_j(\Re B_j)^{-1}<\infty\). Let \(c>0\) and let \(g:(0,\infty)\to(0,\infty)\) satisfy
--   \[g(x)/c=\prod_j(1+x/B_j)\quad(x>0).\]
--   Define \(J(x)=\log g(x)-\log c\) and \(K(t)=\sum_j\Re(e^{-B_jt})\). For \(n\ge1\) and \(u>0\),
--   \[2^n u^{2n-1}(-1)^{n-1}J^{(n)}(u^2)
--   =2^n u^{2n-1}\int_0^\infty t^{n-1}e^{-u^2t}K(t)\,dt.\]
--   The formal index is \(n=r+1\). Neither differentiability of \(g\) nor this integral representation is assumed: both derivative calculations follow from the displayed product identity. The product identity itself remains an explicit hypothesis. Its instantiation for Riemann xi and the complete zeta zero multiset is not claimed by this theorem.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Branch2 Appendix B.1-B.5 and corrected integral representation, PF28. Classical identities; no novelty or RH proof claimed. General spectral formalization, 2026-11-16. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem HadamardLaplacePublished.original_log_Q_from_product (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (g : ℝ → ℝ) (c : ℝ) (hc : 0 < c)
    (hg : ∀ x > 0, 0 < g x)
    (hp : ∀ x > 0, (((g x/c : ℝ) : ℂ)) = ∏' i, (1+(x : ℂ)/B i))
    (r : ℕ) (u : ℝ) (hu : 0 < u) :
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1)*(-1 : ℝ)^r *
      iteratedDeriv (r+1) (fun x => Real.log (g x) - Real.log c) (u^2) =
    (2 : ℝ)^(r+1)*u^(2*(r+1)-1) *
      ∫ t : ℝ in Ioi 0, t^r * Real.exp (-(u^2*t)) *
        ∑' i, (Complex.exp (-(B i*t))).re := by sorry
