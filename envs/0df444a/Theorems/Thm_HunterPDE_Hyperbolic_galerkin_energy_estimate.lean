-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_galerkin_energy_estimate
-- name    : HunterPDE.Hyperbolic.galerkin_energy_estimate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:48:56.815285+00:00
-- url     : https://prove2.me/theorems/3ad60c81-00e5-4fb6-9e2e-0e4ef1709d3a
-- title:
--   Proposition 7.6 — uniform energy estimate (7.10) for the Galerkin approximations
-- statement:
--   Under Assumption 7.1 there is a constant $C$, depending only on $T$, $\Omega$ and the coefficient functions $a^{ij}, c$, such that for every $N \in \mathbb{N}$ the approximate solution $u_N$ of Proposition 7.5 satisfies
--   $$\|u_N\|_{L^\infty(0,T;H^1_0)} + \|u_{Nt}\|_{L^\infty(0,T;L^2)} + \|u_{Ntt}\|_{L^2(0,T;H^{-1})} \le C\big(\|f\|_{L^2(0,T;L^2)} + \|g\|_{H^1_0} + \|h\|_{L^2}\big). \qquad (7.10)$$
--
--   The bound is uniform in $N$, which is what allows passing to a weak-star limit.
--
--   **Formalization Note.** $C$ is a finite constant quantified before the eigenbasis, the data $f, g, h$, $N$ and $u_N$. Norms are `ℝ≥0∞`-valued (`eLpNorm`, `‖·‖ₑ`); $u_{Nt}$ is measured in $L^2(\Omega)$ and $u_{Ntt}$ in $H^{-1}(\Omega)$ through $E_N \subset H^1_0 \hookrightarrow L^2 \hookrightarrow H^{-1}$. The estimate is stated for every approximate solution in the sense of Definition 7.4, which by Proposition 7.5 is the one given there.
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), p. 214, Proposition 7.6, Eq. (7.10)

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator
import Definitions.Def_HunterPDE_Hyperbolic_Galerkin

namespace HunterPDE.Hyperbolic

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Proposition 7.6 (Hunter, p. 214), the uniform energy estimate (7.10). Under Assumption 7.1
there is a constant `C`, depending only on `T`, `Ω` and the coefficients `aᵢⱼ, c` (so chosen
before the Galerkin basis, the data and `N`), such that for every `N ∈ ℕ` the approximate solution
`u_N` of Definition 7.4 satisfies
`‖u_N‖_{L^∞(0,T;H¹₀)} + ‖u_Nt‖_{L^∞(0,T;L²)} + ‖u_Ntt‖_{L²(0,T;H⁻¹)}
  ≤ C (‖f‖_{L²(0,T;L²)} + ‖g‖_{H¹₀} + ‖h‖_{L²})`,
where `u_Nt` is measured in `L²(Ω)` and `u_Ntt` in `H⁻¹(Ω)` (through `E_N ⊂ H¹₀ ⊂ L² ⊂ H⁻¹`).
Norms are `ℝ≥0∞`-valued (`eLpNorm`, `‖·‖ₑ`); `C` is a finite constant. -/
theorem galerkin_energy_estimate {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ)
    (P : Coeffs n) (hA : Assumption71 Ω T P) :
    ∃ C : ℝ≥0, ∀ (w : ℕ → H10 n Ω) (lam : ℕ → ℝ), IsDirichletEigenbasis w lam →
      ∀ (f : ℝ → L2 n Ω), MemLp f 2 (volume.restrict (Ioo 0 T)) →
      ∀ (g : H10 n Ω) (h : L2 n Ω) (N : ℕ) (uN uN_t uN_tt : ℝ → H10 n Ω),
        IsApproxSolution Ω T P w N f g h uN uN_t uN_tt →
        eLpNorm uN ⊤ (volume.restrict (Ioo 0 T)) +
            eLpNorm (fun t => toL2 n Ω (uN_t t)) ⊤ (volume.restrict (Ioo 0 T)) +
            eLpNorm (fun t => l2ToHm1 (toL2 n Ω (uN_tt t))) 2 (volume.restrict (Ioo 0 T)) ≤
          (C : ℝ≥0∞) * (eLpNorm f 2 (volume.restrict (Ioo 0 T)) + ‖g‖ₑ + ‖h‖ₑ) := by sorry

end HunterPDE.Hyperbolic
