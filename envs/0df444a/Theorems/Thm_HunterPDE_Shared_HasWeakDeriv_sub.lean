-- Prove2me | Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_sub
-- name    : HunterPDE.Shared.HasWeakDeriv.sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T22:06:54.555411+00:00
-- url     : https://prove2.me/theorems/a19b75f0-512b-4155-9c93-653641d4377b
-- title:
--   Weak derivatives respect subtraction
-- statement:
--   Let $\Omega\subset\mathbb R^n$, let $\alpha$ be any multi-index, and suppose $u=\partial^\alpha f$ and $v=\partial^\alpha g$ weakly on $\Omega$. Then
--   $$\partial^\alpha(f-g)=u-v.$$
--   Local integrability and the test identities are preserved under subtraction. No openness or Sobolev exponent is needed. This provides the linearity step for derivative convergence in the Shared weak-derivative interface.
-- source:
--   J. K. Hunter, Notes on Partial Differential Equations, revised 6/18/2014, https://www.math.ucdavis.edu/~hunter/pdes/ch3.pdf, Theorems 3.42 and 3.44, printed pp. 72–73. Auxiliary ingredient for the normal Green identity, not an explicit numbered theorem in the source.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory HunterPDE.Shared
open scoped ContDiff
set_option autoImplicit false

theorem HunterPDE.Shared.HasWeakDeriv.sub {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {α : Fin n → ℕ} {f g u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : HasWeakDeriv Ω α f u) (hv : HasWeakDeriv Ω α g v) :
    HasWeakDeriv Ω α (f - g) (u - v) := by sorry
