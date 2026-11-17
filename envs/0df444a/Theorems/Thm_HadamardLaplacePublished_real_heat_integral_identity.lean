-- Prove2me | Theorems.Thm_HadamardLaplacePublished_real_heat_integral_identity
-- name    : HadamardLaplacePublished.real_heat_integral_identity
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:08:36.971237+00:00
-- url     : https://prove2.me/theorems/7ed92849-336c-4af9-8342-d560b537704b
-- title:
--   Summable complex spectrum: heat representation and integrability in every order
-- statement:
--   Suppose \(\Re B_j\ge1\) and \(\sum_j(\Re B_j)^{-1}<\infty\). Set \(K(t)=\sum_j\Re(e^{-B_jt})\) for \(t>0\). For every integer \(r\ge0\) and real \(x\ge0\), the function \(t^r e^{-xt}K(t)\) is integrable on \((0,\infty)\), and
--   \[\int_0^\infty t^r e^{-xt}K(t)\,dt=\Re\!\left(r!\sum_j(x+B_j)^{-r-1}\right).\]
--   The exchange of integral and series is justified by summability of the integrals of the absolute values, including \(r=0\). The assumptions do not assert that the sequence is the zero set of zeta.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Branch2 Appendix B.1-B.5 and corrected integral representation, PF28. Classical identities; no novelty or RH proof claimed. General spectral formalization, 2026-11-16. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem HadamardLaplacePublished.real_heat_integral_identity (B : ℕ → ℂ) (r : ℕ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (x : ℝ) (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) (Ioi 0) ∧
    ((∫ t : ℝ in Ioi 0, t^r * Real.exp (-(x*t)) *
      ∑' i, (Complex.exp (-(B i*t))).re) =
      ((r.factorial : ℂ) * ∑' i, (((x : ℂ)+B i)⁻¹)^(r+1)).re) := by sorry
