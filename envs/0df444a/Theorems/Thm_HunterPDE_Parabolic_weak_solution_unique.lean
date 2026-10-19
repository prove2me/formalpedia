-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_weak_solution_unique
-- name    : HunterPDE.Parabolic.weak_solution_unique
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-17T10:25:47.490066+00:00
-- url     : https://prove2.me/theorems/79955957-5149-421b-afd5-cef64a18d06a
-- title:
--   Uniqueness of weak solutions of the parabolic initial-boundary value problem (Theorem 6.3)
-- statement:
--   Suppose the conditions of Assumption 6.1 hold: $\Omega\subset\mathbb{R}^n$ is bounded and open, $T>0$, and the coefficients $a^{ij}, b^j, c\in L^\infty(\Omega\times(0,T))$ satisfy $a^{ij}=a^{ji}$ and the uniform ellipticity condition (6.6). Let $f\in L^2(0,T;H^{-1}(\Omega))$ and $g\in L^2(\Omega)$. If $u_1$ (with time derivative $u_{1,t}$) and $u_2$ (with $u_{2,t}$) are both weak solutions of (6.8) in the sense of Definition 6.2, with the same data $f$, $g$, then
--
--   $$u_1(t)=u_2(t)\quad\text{in } H^1_0(\Omega)\ \text{for a.e. } t\in(0,T).$$
--
--   Role: this is the uniqueness assertion of Theorem 6.3; existence and the energy estimate come from the Galerkin approximations and their limit.
--
--   **Formalization Note**: uniqueness is as an element of $L^2(0,T;H^1_0(\Omega))$, i.e. almost everywhere for the time measure `timeMeasure T` (Lebesgue measure on $(0,T)$), exactly as in the parent `weak_solution_exists_unique`; `IsWeakSolution` is the published Definition 6.2.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, Theorem 6.3 (uniqueness of the weak solution), pp. 180–181, with Definition 6.2, p. 180

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

namespace HunterPDE.Parabolic

open MeasureTheory

theorem weak_solution_unique {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n) (hP : P.Assumption61 Ω T)
    (f : ℝ → Hm1 n Ω) (g : Lp ℝ 2 (volume.restrict Ω)) (u₁ u₂ : ℝ → H10 n Ω)
    (ut₁ ut₂ : ℝ → Hm1 n Ω) (h₁ : IsWeakSolution Ω T P f g u₁ ut₁)
    (h₂ : IsWeakSolution Ω T P f g u₂ ut₂) :
    u₁ =ᵐ[timeMeasure T] u₂ := by sorry

end HunterPDE.Parabolic
