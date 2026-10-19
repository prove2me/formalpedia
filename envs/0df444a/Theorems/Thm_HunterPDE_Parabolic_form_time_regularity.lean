-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_form_time_regularity
-- name    : HunterPDE.Parabolic.form_time_regularity
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-17T04:51:51.51356+00:00
-- url     : https://prove2.me/theorems/99e6d75d-c22b-41c0-8e72-b1ad6592ff19
-- title:
--   Under Assumption 6.1 the bilinear form $a(u,v;t)$ is a.e. continuous in $v$, integrable in $t$ and weakly continuous in $L^2(0,T;H^1_0)$
-- statement:
--   Let $\Omega\subset\mathbb{R}^n$, $T\in\mathbb{R}$, and let the coefficients $a^{ij}, b^j, c$ satisfy conditions (1)–(2) of Assumption 6.1 on $\Omega\times(0,T)$ (bounded measurable, symmetric uniformly elliptic principal part). Write $a(u,v;t)$ for the bilinear form (6.10) on $H^1_0(\Omega)$. Then:
--
--   1. for almost every $t\in(0,T)$ and every $w\in H^1_0(\Omega)$, the map $v\mapsto a(w,v;t)$ is continuous on $H^1_0(\Omega)$;
--   2. for every measurable $\psi$ with $|\psi|\le B$ on $(0,T)$ ($B\ge 0$), every $v\in H^1_0(\Omega)$ and every $f\in L^2(0,T;H^1_0(\Omega))$, the function $t\mapsto \psi(t)\,a(f(t),v;t)$ is integrable on $(0,T)$;
--   3. for such $\psi$ and $v$, if $x_k\rightharpoonup y$ weakly in $L^2(0,T;H^1_0(\Omega))$ (tested against every $Z\in L^2(0,T;H^1_0(\Omega))$), then
--   $$\int_0^T \psi(t)\,a(x_k(t),v;t)\,dt \;\longrightarrow\; \int_0^T \psi(t)\,a(y(t),v;t)\,dt .$$
--
--   Role: these are the properties of the time-dependent bilinear form used in the proof of Proposition 6.7 to pass to the limit in the Galerkin equations (the form term of the weak equation and of the initial-condition identity) and to extend the limit equation from a dense set of test functions $v$ to all of $H^1_0(\Omega)$.
--
--   **Formalization Note**: weak convergence in $L^2(0,T;H^1_0)$ is stated concretely, as convergence of $\int_0^T (Z(t), x_k(t))_{H^1_0}\,dt$ for every $Z\in L^2(0,T;H^1_0)$, exactly as in the parent `galerkin_limit`; the time measure is Lebesgue measure on $(0,T)$ (`timeMeasure T`).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), https://www.math.ucdavis.edu/~hunter/pdes/pde_notes.pdf, p. 179, Assumption 6.1 and the bilinear form (6.10); used in the proof of Proposition 6.7, p. 186

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

namespace HunterPDE.Parabolic

open MeasureTheory Filter Topology

theorem form_time_regularity {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {T : ℝ} {P : Coeffs n}
    (hP : P.Assumption61 Ω T) :
    (∀ᵐ t ∂(timeMeasure T), ∀ w : H10 n Ω, Continuous (fun v : H10 n Ω => form P t w v)) ∧
    (∀ {ψ : ℝ → ℝ}, Measurable ψ → ∀ {B : ℝ}, 0 ≤ B → (∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) →
      ∀ (v : H10 n Ω) {f : ℝ → H10 n Ω}, MemLp f 2 (timeMeasure T) →
        Integrable (fun t => ψ t * form P t (f t) v) (timeMeasure T)) ∧
    (∀ {ψ : ℝ → ℝ}, Measurable ψ → ∀ {B : ℝ}, 0 ≤ B → (∀ t ∈ Set.Ioo 0 T, |ψ t| ≤ B) →
      ∀ (v : H10 n Ω) {x : ℕ → ℝ → H10 n Ω} {y : ℝ → H10 n Ω},
        (∀ k, MemLp (x k) 2 (timeMeasure T)) → MemLp y 2 (timeMeasure T) →
        (∀ Z : ℝ → H10 n Ω, MemLp Z 2 (timeMeasure T) →
          Tendsto (fun k => ∫ t, inner ℝ (Z t) (x k t) ∂(timeMeasure T)) atTop
            (𝓝 (∫ t, inner ℝ (Z t) (y t) ∂(timeMeasure T)))) →
        Tendsto (fun k => ∫ t in Set.Ioo 0 T, ψ t * form P t (x k t) v) atTop
          (𝓝 (∫ t in Set.Ioo 0 T, ψ t * form P t (y t) v))) := by sorry

end HunterPDE.Parabolic
