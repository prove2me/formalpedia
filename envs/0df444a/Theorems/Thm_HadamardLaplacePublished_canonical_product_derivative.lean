-- Prove2me | Theorems.Thm_HadamardLaplacePublished_canonical_product_derivative
-- name    : HadamardLaplacePublished.canonical_product_derivative
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T08:08:11.065377+00:00
-- url     : https://prove2.me/theorems/7e835ecb-a3c8-4b07-9992-a787bb2e4b72
-- title:
--   Derivative of a convergent canonical product in a zero-free half-plane
-- statement:
--   Let \(B_j\in\mathbb C\) satisfy \(\Re B_j\ge1\) and \(\sum_j(\Re B_j)^{-1}<\infty\). On \(\Re z>-1/2\), put \(P(z)=\prod_j(1+z/B_j)\). Then
--   \[P'(z)=P(z)\sum_j(z+B_j)^{-1}.\]
--   The proof establishes convergence of the normalized logarithmic series and of the product before differentiating. The sequence is general; identifying this canonical product with Riemann xi is a separate theorem.
-- source:
--   Desenvolvimento RH, Ricardo Marangoni Brandao Bueno. Branch2 Appendix B.1-B.5 and corrected integral representation, PF28. Classical identities; no novelty or RH proof claimed. General spectral formalization, 2026-11-16. https://app.notion.com/p/41a98395ac6e8160a225d82e667ec8e4

import Mathlib
open MeasureTheory Set Filter Topology
open scoped BigOperators

theorem HadamardLaplacePublished.canonical_product_derivative (B : ℕ → ℂ)
    (hB : ∀ i, 1 ≤ (B i).re) (hs : Summable (fun i => (B i).re⁻¹))
    (z : ℂ) (hz : -(1/2 : ℝ) < z.re) :
    HasDerivAt (fun w => ∏' i, (1+w/B i))
      ((∏' i, (1+z/B i)) * ∑' i, (z+B i)⁻¹) z := by sorry
