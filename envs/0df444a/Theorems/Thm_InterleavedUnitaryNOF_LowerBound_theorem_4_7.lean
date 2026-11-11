-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_theorem_4_7
-- name    : InterleavedUnitaryNOF.LowerBound.theorem_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:24.456259+00:00
-- url     : https://prove2.me/theorems/ab20fb8e-123e-4981-9884-032371f9d802
-- title:
--   Theorem 4.7 — regularity decomposition, all three clauses
-- statement:
--   Fix $\epsilon>0$ and an integer $d\ge1$. Let $c=fgh$ be a finite-type cylinder on $\mathcal X\times\mathcal Y\times\mathcal Z$, with specified finite equal-measure partitions of the three Haar spaces. There are boxes $B_i=\mathcal X_i\times\mathcal Y_i\times\mathcal Z_i$, $1\le i\le K$, whose coordinates are nonempty unions of the respective cells, and full-space Boolean functions $f_i,g_i$ constant on cell products and supported in $\mathcal Y_i\times\mathcal Z_i$ and $\mathcal X_i\times\mathcal Z_i$, such that
--
--   $$ c=\sum_{i=1}^K f_i g_i h,\qquad \sum_i\mu_0(B_i)\le4(d+3)^2,\qquad K\le\exp(C_\epsilon d^7). $$
--
--   The positive constant $C_\epsilon$ depends only on $\epsilon$. With normalized local densities $\delta_{f,i}$ and $\delta_{g,i}$, every piece either has $\delta_{f,i}\le2^{-d}$ or $\delta_{g,i}\le2^{-d}$, or both functions satisfy $\|u\|_{U(2,d),i}\le(1+\epsilon)\delta_{u,i}$ and every-row mean at least $(1-\epsilon)\delta_{u,i}$. The functions need not be restrictions of the original factors, and boxes may overlap.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: O(d²) total box volume and c_ε depending only on ε → 4(d+3)² total volume and an existential C before d, m, cylinders and partitions; reason: p.22 gives this numerical volume bound and the same d⁷ output exponent
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Theorem 4.7, printed p.12 = PDF p.12; continuation printed/PDF p.13; explicit volume p.22; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem theorem_4_7 (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) [NeZero m]
      (c : Cylinder m) (P : CylinderPartitions c),
      ∃ pieces : List (BoxPiece m),
        (∀ u, bval (c.value u) = (pieces.map (fun B => B.value c.h u)).sum) ∧
        (∀ B ∈ pieces, RespectsPartitions P B) ∧
        (pieces.map BoxPiece.volume).sum ≤ 4*((d : ℝ)+3)^2 ∧
        (pieces.length : ℝ) ≤ Real.exp (C*(d : ℝ)^7) ∧
        (∀ B ∈ pieces, B.df ≤ Real.rpow 2 (-(d : ℝ)) ∨
          B.dg ≤ Real.rpow 2 (-(d : ℝ)) ∨ B.Pseudorandom ε d) := by sorry

end InterleavedUnitaryNOF.LowerBound
