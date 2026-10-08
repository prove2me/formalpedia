-- Prove2me | Theorems.Thm_GabayMercier_Approximation_eq_4_5
-- name    : GabayMercier.Approximation.eq_4_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:26.273412+00:00
-- url     : https://prove2.me/theorems/cdce5229-9987-4311-8901-0519682bdb15
-- title:
--   Equation (4.5) — corrected zero-competitor estimate
-- statement:
--   Under the standing assumptions and (4.1)–(4.3), let $w\in V_k$ solve $({\cal P}_k)$ and suppose $f_2(0)<+\infty$. Choosing the zero competitor in (4.4) yields
--   $$
--   \|A_kw\|^2-\langle b,w\rangle+f_2(A_kw)\le f_2(0).
--   $$
--   This is the estimate used to bound discrete solutions.
--
--   **Formalization Note** The paper prints $f_2(A_kw)-f_2(0)$ on the right of (4.5). Substitution in (4.4) gives $f_2(0)-f_2(A_kw)$ instead. The finite-value assumption on $f_2(0)$ is explicit here and is not added to Theorem 4.1.
-- source:
--   Gabay & Mercier, IRIA RR-126 (1975), hal-04716124v1, p. 21, (4.5)

import Mathlib
import Definitions.Def_InertialFB_IFB_ConvexAnalysis
import Definitions.Def_GabayMercier_Approximation_Model

open Filter Topology InertialFB.IFB

namespace GabayMercier.Approximation

variable {V Y : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- (4.5), with the sign corrected by setting the competitor in (4.4) to zero. -/
theorem eq_4_5 (A : V →L[ℝ] Y) (f₂ : Y → EReal) (b : StrongDual ℝ V)
    (α : ℝ) (Vh : ℕ → Submodule ℝ V) [∀ k, FiniteDimensional ℝ (Vh k)]
    (Ah : (k : ℕ) → Vh k →L[ℝ] Y) (α' M : ℝ)
    (h : ApproxHyp A f₂ α Vh Ah α' M) (hzero : f₂ 0 ≠ ⊤)
    (k : ℕ) (w : Vh k) (hw : IsSolutionH (Ah k) f₂ b w) :
    (((‖Ah k w‖ ^ 2 - b w : ℝ) : EReal) + f₂ (Ah k w)) ≤ f₂ 0 := by sorry

end GabayMercier.Approximation
