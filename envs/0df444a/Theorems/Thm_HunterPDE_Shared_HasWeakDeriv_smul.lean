-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_smul
-- name    : HunterPDE.Shared.HasWeakDeriv.smul
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-18T16:32:45.09037+00:00
-- url     : https://prove2.me/theorems/b8ac2d35-b848-4cb5-b114-1497dc824155
-- title:
--   Scalar multiplication preserves weak derivatives
-- statement:
--   If $g$ is the weak derivative of $f$ of multi-index $\alpha$ on a subset $\Omega$ of Euclidean space, then $cg$ is the same weak derivative of $cf$ for every real scalar $c$. Both local integrability conditions and the test-function identity are preserved. No openness assumption on $\Omega$ is required.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations (2014), https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Definitions 3.1–3.2, pp.47–48; linearity of the defining integral identity.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.smul {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (h : HasWeakDeriv Ω α f g) (c : ℝ) :
    HasWeakDeriv Ω α (c • f) (c • g) := by sorry
