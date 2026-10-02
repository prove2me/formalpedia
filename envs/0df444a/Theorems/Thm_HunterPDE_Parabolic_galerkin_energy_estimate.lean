-- Prove2me | Theorems.Thm_HunterPDE_Parabolic_galerkin_energy_estimate
-- name    : HunterPDE.Parabolic.galerkin_energy_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:21:45.930032+00:00
-- url     : https://prove2.me/theorems/6f4169cc-9369-4543-987e-5e69c73d046d
-- title:
--   Proposition 6.6 — energy estimate for the Galerkin approximations, uniform in N
-- statement:
--   Under Assumption 6.1 ($\Omega \subset \mathbb{R}^n$ bounded and open, $T > 0$, coefficients $a^{ij}, b^j, c$ as in (1)–(2)), there is a constant $C$, depending only on $T$, $\Omega$ and the coefficient functions $a^{ij}, b^j, c$, such that for every Dirichlet eigenbasis $\{w_k\}$, every $f \in L^2(0,T;H^{-1}(\Omega))$, $g \in L^2(\Omega)$ and every $N \in \mathbb{N}$, the approximate solution $u_N$ of Definition 6.4 satisfies
--   $$\|u_N\|_{L^\infty(0,T;L^2)} + \|u_N\|_{L^2(0,T;H^1_0)} + \|u_{Nt}\|_{L^2(0,T;H^{-1})} \le C\big(\|f\|_{L^2(0,T;H^{-1})} + \|g\|_{L^2}\big).$$
--
--   The uniformity in $N$ is what allows a weakly convergent subsequence to be extracted.
--
--   **Formalization Note.** $C \ge 0$ is quantified after $\Omega$, $T$ and the coefficients and before the basis, $f$, $g$, $N$ and $u_N$. Norms are `eLpNorm` over $(0,T)$ with values in $[0,\infty]$; $u_{Nt}(t) \in E_N$ is measured in $H^{-1}$ through $v \mapsto (u_{Nt}(t), v)_{L^2}$. The $H^1_0$ norm is the full $H^1$ norm. The estimate is stated for every approximate solution, which is the one of Proposition 6.5 by uniqueness.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 184, Proposition 6.6

import Mathlib
import Definitions.Def_HunterPDE_Parabolic_H10
import Definitions.Def_HunterPDE_Parabolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Parabolic_WeakSolution

open MeasureTheory
open scoped ENNReal NNReal

namespace HunterPDE.Parabolic

/-- Proposition 6.6 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 184 (uniform energy
estimate): under Assumption 6.1, there is a constant `C`, depending only on `T`, `Ω` and the
coefficient functions `aⁱʲ, bʲ, c`, such that for every `N ∈ ℕ` the approximate solution `u_N`
(Definition 6.4, constructed in Proposition 6.5) satisfies
`‖u_N‖_{L^∞(0,T;L²)} + ‖u_N‖_{L²(0,T;H¹₀)} + ‖u_{Nt}‖_{L²(0,T;H⁻¹)} ≤ C (‖f‖_{L²(0,T;H⁻¹)} + ‖g‖_{L²})`.
`C` is quantified after `Ω, T` and the coefficients and before the Galerkin basis, `f`, `g`,
`N` and `u_N`. Norms are in `ℝ≥0∞`; `u_{Nt}(t) ∈ E_N ⊂ H¹₀` is measured in `H⁻¹` through
`H¹₀ ↪ L² ↪ H⁻¹`, and the `H¹₀` norm is the full `H¹` norm. -/
theorem galerkin_energy_estimate {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) (T : ℝ) (hT : 0 < T) (P : Coeffs n)
    (hP : P.Assumption61 Ω T) :
    ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (eig : ℕ → ℝ), IsDirichletEigenbasis Ω w eig →
      ∀ f : ℝ → Hm1 n Ω, MemLp f 2 (timeMeasure T) →
      ∀ (g : Lp ℝ 2 (volume.restrict Ω)) (N : ℕ) (uN uNt : ℝ → H10 n Ω),
        IsApproxSolution Ω T P w N f g uN uNt →
        eLpNorm (fun t => toL2 (uN t)) ∞ (timeMeasure T) + eLpNorm uN 2 (timeMeasure T) +
            eLpNorm (fun t => l2Embed n Ω (uNt t)) 2 (timeMeasure T) ≤
          (C : ℝ≥0∞) * (eLpNorm f 2 (timeMeasure T) + ‖g‖ₑ) := by sorry

end HunterPDE.Parabolic
