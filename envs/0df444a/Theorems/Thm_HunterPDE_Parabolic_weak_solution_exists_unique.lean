-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_weak_solution_exists_unique
-- name    : HunterPDE.Parabolic.weak_solution_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:26:23.587851+00:00
-- url     : https://prove2.me/theorems/4517f936-c14f-4236-829d-a75395f4e951
-- title:
--   Theorem 6.3 — existence, uniqueness and energy estimate for weak solutions of the parabolic IBVP
-- statement:
--   Let $\Omega \subset \mathbb{R}^n$ be bounded and open and $T > 0$. Let $L u = -\sum_{i,j}\partial_i(a^{ij}\partial_j u) + \sum_j b^j\partial_j u + cu$ with $a^{ij}, b^j, c \in L^\infty(\Omega\times(0,T))$, $a^{ij} = a^{ji}$, and $\sum_{i,j} a^{ij}\xi_i\xi_j \ge \theta|\xi|^2$ for some $\theta > 0$ (Assumption 6.1). Then for every $f \in L^2(0,T;H^{-1}(\Omega))$ and $g \in L^2(\Omega)$ there is a unique weak solution
--   $$u \in C([0,T];L^2(\Omega)) \cap L^2(0,T;H^1_0(\Omega)), \qquad u_t \in L^2(0,T;H^{-1}(\Omega)),$$
--   of $u_t + Lu = f$ in $\Omega\times(0,T)$, $u = 0$ on $\partial\Omega$, $u(0) = g$, in the sense of Definition 6.2. Moreover, there is a constant $C$, depending only on $\Omega$, $T$ and the coefficients of $L$, such that
--   $$\|u\|_{L^\infty(0,T;L^2)} + \|u\|_{L^2(0,T;H^1_0)} + \|u_t\|_{L^2(0,T;H^{-1})} \le C\big(\|f\|_{L^2(0,T;H^{-1})} + \|g\|_{L^2}\big).$$
--
--   This is the basic well-posedness theorem for linear second-order parabolic equations in divergence form.
--
--   **Formalization Note.** The printed statement takes $g \in H^1_0(\Omega)$; Assumption 6.1(3), which the theorem invokes, the $\|g\|_{L^2}$ in the estimate, and the proof (pp. 183–188) all take $g \in L^2(\Omega)$, and that is what is stated (it contains the printed case). $C \ge 0$ is quantified after $\Omega$, $T$ and the coefficients and before $f$, $g$. Uniqueness is as an element of $L^2(0,T;H^1_0(\Omega))$: two weak solutions agree for a.e. $t \in (0,T)$. Membership in $C([0,T];L^2(\Omega))$ is part of `IsWeakSolution` (the continuous representative through which $u(0) = g$ is read). Norms are `eLpNorm` over $(0,T)$ with values in $[0,\infty]$.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 180–181, Theorem 6.3

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic

/-- Theorem 6.3 of Hunter, *Notes on PDEs* (revised 6/18/2014), pp. 180–181: suppose the
conditions of Assumption 6.1 hold (`Ω ⊂ ℝⁿ` bounded and open, `T > 0`, `aⁱʲ, bʲ, c ∈ L^∞(Ω × (0, T))`,
`aⁱʲ = aʲⁱ`, uniform ellipticity (6.6) with some `θ > 0`). Then for every `f ∈ L²(0, T; H⁻¹(Ω))`
and `g ∈ L²(Ω)` there is a unique weak solution `u ∈ C([0, T]; L²(Ω)) ∩ L²(0, T; H¹₀(Ω))` of
(6.8), in the sense of Definition 6.2, with `u_t ∈ L²(0, T; H⁻¹(Ω))`; moreover there is a
constant `C`, depending only on `Ω`, `T` and the coefficients of `L`, such that
`‖u‖_{L^∞(0,T;L²)} + ‖u‖_{L²(0,T;H¹₀)} + ‖u_t‖_{L²(0,T;H⁻¹)} ≤ C (‖f‖_{L²(0,T;H⁻¹)} + ‖g‖_{L²})`.

The printed statement takes `g ∈ H¹₀(Ω)`; Assumption 6.1(3), the estimate (which uses
`‖g‖_{L²}`) and the proof (pp. 183–188) take `g ∈ L²(Ω)`, which is what is stated here (it
contains the printed case). `C` is quantified before `f` and `g`. Uniqueness is as an element of
`L²(0, T; H¹₀(Ω))`: two weak solutions agree for a.e. `t ∈ (0, T)`. Continuity in time,
`u ∈ C([0, T]; L²(Ω))`, is part of `IsWeakSolution` (the continuous representative through which
`u(0) = g` is read). -/
theorem weak_solution_exists_unique {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ g : Lp ℝ 2 (volume.restrict Ω),
        (∃ (u : ℝ → H10 n Ω) (ut : ℝ → Hm1 n Ω), IsWeakSolution Ω T P f g u ut ∧
          eLpNorm (fun t => toL2 (u t)) ∞ (timeMeasure T) + eLpNorm u 2 (timeMeasure T) +
              eLpNorm ut 2 (timeMeasure T) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ)) ∧
        ∀ (u₁ u₂ : ℝ → H10 n Ω) (ut₁ ut₂ : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g u₁ ut₁ → IsWeakSolution Ω T P f g u₂ ut₂ →
            u₁ =ᵐ[timeMeasure T] u₂ := by sorry

end HunterPDE.Parabolic
