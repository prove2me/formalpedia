-- Prove2me | Theorems.Thm_InterleavedUnitaryNOF_LowerBound_corollary_4_13
-- name    : InterleavedUnitaryNOF.LowerBound.corollary_4_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:10:08.335211+00:00
-- url     : https://prove2.me/theorems/63b0e02e-c8e0-4b2e-8c72-75e08e87abcb
-- title:
--   Corollary 4.13 — localized grid-norm bound
-- statement:
--   There are universal $\lambda>1$ and $\kappa>0$. Let $B_i=\mathcal X_i\times\mathcal Y_i\times\mathcal Z_i$ have positive product Haar measure, let $f_i,g_i$ be measurable Boolean factors supported on their respective coordinate pairs, and let $h_i=h1_{\mathcal X_i}1_{\mathcal Y_i}$ for a measurable Boolean $h$. Write $c_i=f_ig_ih_i$ and $\delta_{h,i}$ for the normalized local mean of $h_i$. For every integer $p\ge2$,
--
--   $$\mu_1(c_i)\le\lambda^{1+2/p}\mu_0(B_i)\delta_{h,i}^{1-1/p}\|f_i\|_{U(2,p),i}\|g_i\|_{U(2,p),i}+e^{-\kappa\sqrt m/p}.$$
--
--   All local norms use Haar measure normalized separately on each coordinate set. This includes every piece of Theorem 4.7.
--
--   Differences from the source:
--   - encoding: positive matrix dimension and measurable Boolean functions on SU(m) powers → Fin m with NeZero m, normalized Borel Haar on the actual matrix group, and Bool indicators valued in ℝ; reason: these represent exactly the source objects, including m=1, without a discretization of the group
--   - generalization: boxes and factors in the source decomposition → all measurable supported Boolean pairs on positive-measure boxes; reason: the normalization argument on p.17 applies to these boxes and specializes to every source piece
--   - encoding: λ and κ from the global grid bound → positive existential constants uniform over all local boxes and moments; reason: common global and local witnesses are obtained by increasing λ and decreasing κ; no prior theorem is assumed
-- source:
--   Haoyu Wang, Pei Wu, Guangxu Yang, STOC 2027 submission #1513 (October 2026), Corollary 4.13, printed p.16 = PDF p.16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1513.pdf

import Mathlib
import Definitions.Def_InterleavedUnitaryNOF_LowerBound_Regularity

open MeasureTheory

namespace InterleavedUnitaryNOF.LowerBound

theorem corollary_4_13 : ∃ lam κ : ℝ, 1 < lam ∧ 0 < κ ∧
    ∀ (m : ℕ) [NeZero m] (B : BoxPiece m), B.Positive →
      ∀ (h : Quart m × Quart m → Bool), Measurable h → ∀ (p : ℕ), 2 ≤ p →
      (∫ u, B.value h u ∂mu1 m) ≤
        Real.rpow lam (1+2/(p : ℝ)) * B.volume * Real.rpow (B.dh h) (1-1/(p : ℝ)) *
          gridNorm B.yLaw B.zLaw (bval ∘ B.f) p *
          gridNorm B.xLaw B.zLaw (bval ∘ B.g) p +
        Real.exp (-κ*Real.sqrt m/(p : ℝ)) := by sorry

end InterleavedUnitaryNOF.LowerBound
