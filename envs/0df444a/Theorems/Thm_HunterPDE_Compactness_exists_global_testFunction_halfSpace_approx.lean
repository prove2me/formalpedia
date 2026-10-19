-- Prove2me | Theorems.Thm_HunterPDE_Compactness_exists_global_testFunction_halfSpace_approx
-- name    : HunterPDE.Compactness.exists_global_testFunction_halfSpace_approx
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:06:31.843979+00:00
-- url     : https://prove2.me/theorems/b3ed7886-efbd-4eed-9268-4900af9f11e4
-- title:
--   Half-space approximation by whole-space test functions
-- statement:
--   For $m,k\in\mathbb N$, $1\le p<\infty$, $f\in W^{k,p}(\mathbb R^{m+1}_+)$, and every positive extended-real $\varepsilon$, there is a whole-space smooth compactly supported function $\varphi$ whose restriction belongs to $W^{k,p}(\mathbb R^{m+1}_+)$ and
--   $$\|f-\varphi\|_{W^{k,p}(\mathbb R^{m+1}_+)}<\varepsilon.$$
--   The approximants may meet the boundary. This strengthens the existing density interface by retaining whole-space test regularity and Sobolev membership, as delivered by extension, smoothing and compact cutoff.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorems 3.42 and 3.44, printed pp. 72–73. Auxiliary ingredient for the normal Green identity, not an explicit numbered theorem in the source.

import Theorems.Thm_HunterPDE_Compactness_exists_sobolev_extension_halfSpace
import Theorems.Thm_HunterPDE_Compactness_sobolevNorm_restrict_le
import Theorems.Thm_HunterPDE_Sobolev_smooth_approximation
import Theorems.Thm_HunterPDE_Sobolev_smooth_compact_cutoff_approximation
import Theorems.Thm_HunterPDE_Sobolev_sobolevNorm_sub_triangle
import Theorems.Thm_HunterPDE_Sobolev_HasWeakDeriv_sub
import Theorems.Thm_HunterPDE_Compactness_memW_iff_sobolev
import Theorems.Thm_HunterPDE_Sobolev_memW_of_isTestFunction
import Theorems.Thm_HunterPDE_Sobolev_IsTestFunction_iteratedPartial

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Compactness.exists_global_testFunction_halfSpace_approx (m k : ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ) (hf : MemW k p (upperHalfSpace m) f)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ φ : EuclideanSpace ℝ (Fin (m + 1)) → ℝ, HunterPDE.Shared.IsTestFunction Set.univ φ ∧ MemW k p (upperHalfSpace m) φ ∧
      sobolevNorm k p (upperHalfSpace m) (f - φ) < ε := by sorry
