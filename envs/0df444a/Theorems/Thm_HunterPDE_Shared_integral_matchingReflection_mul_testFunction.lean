-- Prove2me | Theorems.Thm_HunterPDE_Shared_integral_matchingReflection_mul_testFunction
-- name    : HunterPDE.Shared.integral_matchingReflection_mul_testFunction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T09:39:13.710376+00:00
-- url     : https://prove2.me/theorems/b6955110-f590-4bca-9664-35c3ca3ca427
-- title:
--   Moment cancellation gives the weak identity for a reflected multi-derivative
-- statement:
--   Let H={x_i>0}, let alpha be a multi-index, and suppose 1<=p<=infinity. Assume f and g belong to Lp(H) and g is the weak alpha derivative of f on H. Let T_j multiply coordinate i by -b_j, with b_j>0, and let the coefficients satisfy sum_j c_j(-b_j)^r=1 for every integer 0<=r<alpha_i. Define F=f on H and F=sum_j c_j f(T_j x) below the boundary, and define G=g on H and G=sum_j c_j(-b_j)^(alpha_i) g(T_j x) below the boundary. For every smooth compactly supported test function phi on the whole space,
--   $$\int G\phi=(-1)^{|\alpha|}\int F\,\partial^\alpha\phi.$$
--   There is no Sobolev-membership assumption on all lower derivatives, and when alpha_i=0 the moment condition is empty. This is a proposed boundary cancellation lemma; it remains to be proved. One route is normal change of variables followed by testing the interior weak identity against an adjoint folded test whose first alpha_i normal jets vanish, using normal cutoffs and local L1 convergence. No density theorem depending on the extension may be used.
-- source:
--   Sung-Jin Oh, Lecture Notes for Math 222A, March 19, 2024, Proposition 11.13, proof Step 2, printed p. 158, equations (11.3)-(11.4), https://math.berkeley.edu/~sjoh/pdfs/notes-math222a.pdf . Distributional form of the matching-derivative construction, for a single specified multi-index and arbitrary weak data. The passage from interior test functions to boundary-compatible tests is an explicit remaining proof obligation, not a consequence attributed to the smooth calculation alone.

import Definitions.Def_HunterPDE_Shared_WeakDeriv
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem HunterPDE.Shared.integral_matchingReflection_mul_testFunction
    {n N : ℕ} (i : Fin n) (α : Fin n → ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (hc : ∀ r : ℕ, r < α i → ∑ j : Fin N, c j * (-b j) ^ r = 1)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i}))
    (hg : MemLp g p (volume.restrict {x | 0 < x i}))
    (hd : HunterPDE.Shared.HasWeakDeriv {x | 0 < x i} α f g)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : HunterPDE.Shared.IsTestFunction Set.univ φ) :
    (∫ x, (if 0 < x i then g x else
      ∑ j : Fin N, (c j * (-b j) ^ (α i)) *
        g (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) * φ x) =
    (-1 : ℝ) ^ (∑ l, α l) *
      ∫ x, (if 0 < x i then f x else
        ∑ j : Fin N, c j *
          f (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) *
        HunterPDE.Shared.multiDeriv φ α x := by sorry
