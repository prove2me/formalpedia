-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_weak_solution_unique
-- name    : HunterPDE.Hyperbolic.weak_solution_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:52:42.212995+00:00
-- url     : https://prove2.me/theorems/4a3129d0-4314-43ba-9727-582105565de7
-- title:
--   Proposition 7.12 — uniqueness of weak solutions of the hyperbolic IBVP (7.5)
-- statement:
--   Under Assumption 7.1, with $f \in L^2(0,T;L^2(\Omega))$, $g \in H^1_0(\Omega)$, $h \in L^2(\Omega)$: a weak solution of (7.5) in the sense of Definition 7.2 is unique. That is, if $u$ and $u'$ are weak solutions with the same data, then
--   $$u'(t) = u(t) \qquad \text{for all } t \in [0,T].$$
--
--   Uniqueness cannot be obtained by testing the equation with $u_t$, which is only in $L^2(\Omega)$; together with the Galerkin construction it completes Theorem 7.3.
--
--   **Formalization Note.** The two solutions may come with any weak derivatives $u_t, u_{tt}$ and $u'_t, u'_{tt}$ satisfying Definition 7.2.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 220, Proposition 7.12

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator

namespace HunterPDE.Hyperbolic

open MeasureTheory Set

/-- Proposition 7.12 (Hunter, p. 220). Under Assumption 7.1, with `f ∈ L²(0, T; L²(Ω))`,
`g ∈ H¹₀(Ω)`, `h ∈ L²(Ω)`, a weak solution of (7.5) in the sense of Definition 7.2 is unique:
two weak solutions `u, u'` (with any weak derivatives) coincide on `[0, T]`. -/
theorem weak_solution_unique {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ)
    (P : Coeffs n) (hA : Assumption71 Ω T P)
    (f : ℝ → L2 n Ω) (hf : MemLp f 2 (volume.restrict (Ioo 0 T))) (g : H10 n Ω) (h : L2 n Ω)
    (u : ℝ → H10 n Ω) (u_t : ℝ → L2 n Ω) (u_tt : ℝ → Hm1 n Ω)
    (u' : ℝ → H10 n Ω) (u'_t : ℝ → L2 n Ω) (u'_tt : ℝ → Hm1 n Ω)
    (hsol : IsWeakSolution Ω T P f g h u u_t u_tt)
    (hsol' : IsWeakSolution Ω T P f g h u' u'_t u'_tt) :
    ∀ t ∈ Icc 0 T, u' t = u t := by sorry

end HunterPDE.Hyperbolic
