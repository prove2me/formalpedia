-- Prove2me | Theorems.Thm_GabayMercier_Approximation_weak_limit_eq
-- name    : GabayMercier.Approximation.weak_limit_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:22.104384+00:00
-- url     : https://prove2.me/theorems/398804e3-52e0-4000-b6e8-64eda25bac7c
-- title:
--   Equation (4.7) — every weak cluster point is the solution
-- statement:
--   Assume the hypotheses of Theorem 4.1 and let $v^*$ solve $({\cal P})$. Let $v_k^*$ be any eventual family of discrete solutions. If a subsequence indexed by a strictly increasing map $\varphi:\mathbb N\to\mathbb N$ converges weakly in $V$ to $w$, then
--   $$
--   w=v^*.
--   $$
--   This is the identification of the weak limit obtained after (4.7). It is the step that excludes distinct weak cluster points.
--
--   **Formalization Note** The paper's displayed inequality (4.7) uses a liminf of extended-valued expressions. The Lean statement records its stated consequence for every weakly convergent subsequence; weak convergence is tested by all Hilbert-space inner products.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 21, (4.7), continued p. 22

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- The identification of each weak subsequential limit after (4.7). -/
theorem weak_limit_eq (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (vs : V)
    (hvs : GabayMercier.DualAlgorithm.IsSolution A halfSq f₂ b vs)
    (vh : (k : ℕ) → Vh k) (hvh : ∀ᶠ k in atTop, IsSolutionH (Ah k) f₂ b (vh k))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (w : V)
    (hw : WeakTendsto (fun k => (vh (φ k) : V)) w) : w = vs := by sorry

end GabayMercier.Approximation
