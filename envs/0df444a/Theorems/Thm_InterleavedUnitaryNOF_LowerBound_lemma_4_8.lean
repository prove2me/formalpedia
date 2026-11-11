-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_lemma_4_8
-- name    : InterleavedUnitaryNOF.LowerBound.lemma_4_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:14.424015+00:00
-- url     : https://prove2.me/theorems/1f5a0054-e4c8-4d75-b4b1-a42efdc57a11
-- title:
--   Lemma 4.8 — regular pieces
-- statement:
--   There are universal $\kappa>0$ and $\alpha>1$ with the following property. Let $0<\epsilon\le10^{-4}$ and $d\ge8/\epsilon$. Let $B_i=\mathcal X_i\times\mathcal Y_i\times\mathcal Z_i$ be a supported finite-type piece, with Boolean $f_i,g_i$ both $(\epsilon,d)$-regular and satisfying $\epsilon$-min-degree on their normalized local domains. Let $h_i=h1_{\mathcal X_i}1_{\mathcal Y_i}$, $c_i=f_ig_ih_i$, and let $\delta_{f,i},\delta_{g,i},\delta_{h,i}$ be their local densities. If $\delta_{f,i},\delta_{g,i}>2^{-d}$ and $\delta_{h,i}>2^{-\epsilon d}$, then
--
--   $$ \mu_1(c_i)\le\alpha\mu_0(c_i)+\exp(-\kappa\sqrt m/d). $$
--
--   All constants are independent of the piece, partitions, parameters and dimension.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - encoding: sufficiently small positive ε and sufficiently large d in the p.13 preamble → 0<ε≤10⁻⁴ and d≥8/ε; reason: the proof fixes exactly this regime on pp.17–18; it is not imposed on the goal
--   - generalization: a regular-index piece of the source decomposition → any supported cell-constant piece with the same local regularity, min-degree and three density inequalities; reason: the local estimate on pp.17–18 uses only these properties; every source regular piece supplies them
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Lemma 4.8, printed p.13 = PDF p.13; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem lemma_4_8 : ∃ κ α : ℝ, 0 < κ ∧ 1 < α ∧
    ∀ (m : ℕ) [NeZero m] (ε : ℝ), 0 < ε → ε ≤ (1 : ℝ)/10000 →
      ∀ (d : ℕ), 8/ε ≤ (d : ℝ) → ∀ (c : Cylinder m) (P : CylinderPartitions c)
      (B : BoxPiece m), RespectsPartitions P B → B.Pseudorandom ε d →
      Real.rpow 2 (-(d : ℝ)) < B.df → Real.rpow 2 (-(d : ℝ)) < B.dg →
      Real.rpow 2 (-ε*d) < B.dh c.h →
      (∫ u, B.value c.h u ∂mu1 m) ≤ α*(∫ u, B.value c.h u ∂mu0 m) +
        Real.exp (-κ*Real.sqrt m/(d : ℝ)) := by sorry

end InterleavedUnitaryNOF.LowerBound
