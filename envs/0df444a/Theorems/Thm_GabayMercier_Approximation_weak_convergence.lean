-- Prove2me | Theorems.Thm_GabayMercier_Approximation_weak_convergence
-- name    : GabayMercier.Approximation.weak_convergence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:52.529447+00:00
-- url     : https://prove2.me/theorems/3718e4ad-b16b-49c8-988a-19b9383b925c
-- title:
--   Weak convergence of the discrete solutions
-- statement:
--   Under the hypotheses of Theorem 4.1, let $v^*$ solve $({\cal P})$ and choose any $v_k^*\in V_k$ solving $({\cal P}_k)$ for all sufficiently large $k$. Then
--   $$
--   v_k^*\rightharpoonup v^*\quad\text{weakly in }V.
--   $$
--   This is the paper's conclusion after identifying each weak cluster point in (4.7), without retaining a subsequence. It supports the later strong-convergence estimate.
--
--   **Formalization Note** Weak convergence uses the published `WeakTendsto` predicate. The statement quantifies over every eventual choice of discrete solutions.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 22, paragraph following (4.7)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The unrestricted weak convergence following (4.7). -/
theorem weak_convergence (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k)) :
    WeakTendsto (fun k => (vh k : V)) vs := by sorry

end GabayMercier.Approximation
