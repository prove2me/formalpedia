-- Prove2me | Theorems.Thm_HunterPDE_Sobolev_exists_smooth_ae_approx_gradient_bound
-- name    : HunterPDE.Sobolev.exists_smooth_ae_approx_gradient_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T17:21:34.718546+00:00
-- url     : https://prove2.me/theorems/d3460e81-feb9-4605-a1c0-bb31037bdbf4
-- title:
--   Smooth a.e. approximation preserving a homogeneous weak gradient bound
-- statement:
--   Let $n\ge1$, $1\le p<\infty$, and let $f$ have all weak first partial derivatives in $L^p(\mathbb R^n)$. If the Euclidean length of its weak gradient has $L^p$ norm at most $C\ge0$, there is a sequence of globally smooth functions $v_j$ converging to $f$ almost everywhere, with $\|Dv_j\|_p\le C$ for every $j$. No global integrability or decay assumption is imposed on $f$. Compactly supported nonnegative probability mollifiers provide the approximants: commute weak derivatives with convolution, use convexity of the Euclidean norm and Young’s inequality, and choose scales tending to zero. This interface isolates homogeneous smoothing, independently of Morrey or continuous representatives.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, printed pp. 68–70, Theorems 3.36–3.37; homogeneous mollification and dense-set extension in the proof of Theorem 3.37.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
open MeasureTheory Filter
open scoped Topology ENNReal NNReal

theorem HunterPDE.Sobolev.exists_smooth_ae_approx_gradient_bound {n : ℕ} (hn : 1 ≤ n)
    (p : ℝ) (hp : 1 ≤ p) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i : Fin n, ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      HunterPDE.Shared.HasWeakDeriv Set.univ (Pi.single i 1) f g ∧
        MemLp g (ENNReal.ofReal p) volume)
    (C : ℝ≥0)
    (hC : eLpNorm (HunterPDE.Shared.weakGradNorm Set.univ f) (ENNReal.ofReal p) volume ≤
      (C : ℝ≥0∞)) :
    ∃ v : ℕ → EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ j, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (v j)) ∧
      (∀ j, eLpNorm (fun z => ‖gradient (v j) z‖) (ENNReal.ofReal p) volume ≤
        (C : ℝ≥0∞)) ∧
      ∀ᵐ x ∂volume, Tendsto (fun j => v j x) atTop (𝓝 (f x)) := by sorry
