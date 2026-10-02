-- Prove2me | Theorems.Thm_HunterPDE_Hyperbolic_hyperbolic_existence_uniqueness
-- name    : HunterPDE.Hyperbolic.hyperbolic_existence_uniqueness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:53:38.016482+00:00
-- url     : https://prove2.me/theorems/b04f23e0-d5df-4511-85c4-37fb73f569f0
-- title:
--   Theorem 7.3 — existence, uniqueness and energy estimate for weak solutions of second-order hyperbolic PDEs
-- statement:
--   Suppose that the conditions in Assumption 7.1 are satisfied. Then for every $f \in L^2(0,T;L^2(\Omega))$, $g \in H^1_0(\Omega)$ and $h \in L^2(\Omega)$ there is a unique weak solution $u$ of
--   $u_{tt} + Lu = f$ in $\Omega\times(0,T)$, $u = 0$ on $\partial\Omega\times(0,T)$, $u = g$, $u_t = h$ at $t = 0$ (7.5), in the sense of Definition 7.2. Moreover, there is a constant $C$, depending only on $\Omega$, $T$ and the coefficients of $L$, such that
--   $$\|u\|_{L^\infty(0,T;H^1_0)} + \|u_t\|_{L^\infty(0,T;L^2)} + \|u_{tt}\|_{L^2(0,T;H^{-1})} \le C\big(\|f\|_{L^2(0,T;L^2)} + \|g\|_{H^1_0} + \|h\|_{L^2}\big).$$
--
--   This is the basic well-posedness theorem for linear second-order hyperbolic equations with time-dependent coefficients in energy spaces, the hyperbolic counterpart of the parabolic existence theorem of Chapter 6.
--
--   **Formalization Note.** $C$ is a finite constant quantified after $\Omega, T$ and the coefficients and before $f, g, h$. Uniqueness is stated as: every weak solution coincides with $u$ on $[0,T]$. Norms are `ℝ≥0∞`-valued (`eLpNorm` over $(0,T)$, `‖·‖ₑ`).
-- source:
--   Hunter, Notes on Partial Differential Equations (revised 6/18/2014), pp. 213–214, Theorem 7.3

import Mathlib
import Definitions.Def_HunterPDE_Hyperbolic_H10
import Definitions.Def_HunterPDE_Hyperbolic_WeakTimeDeriv
import Definitions.Def_HunterPDE_Hyperbolic_WaveOperator

namespace HunterPDE.Hyperbolic

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Theorem 7.3 (Hunter, pp. 213–214). Suppose that Assumption 7.1 holds. Then there is a constant
`C`, depending only on `Ω`, `T` and the coefficients of `L` (so chosen before the data), such that
for every `f ∈ L²(0, T; L²(Ω))`, `g ∈ H¹₀(Ω)` and `h ∈ L²(Ω)` there is a weak solution
`u` of (7.5) in the sense of Definition 7.2 (with weak derivatives `u_t`, `u_tt`), it is unique
(every weak solution coincides with `u` on `[0, T]`), and
`‖u‖_{L^∞(0,T;H¹₀)} + ‖u_t‖_{L^∞(0,T;L²)} + ‖u_tt‖_{L²(0,T;H⁻¹)}
  ≤ C (‖f‖_{L²(0,T;L²)} + ‖g‖_{H¹₀} + ‖h‖_{L²})`.
Norms are `ℝ≥0∞`-valued (`eLpNorm`, `‖·‖ₑ`); `C` is a finite constant. -/
theorem hyperbolic_existence_uniqueness {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (T : ℝ)
    (P : Coeffs n) (hA : Assumption71 Ω T P) :
    ∃ C : ℝ≥0, ∀ (f : ℝ → L2 n Ω), MemLp f 2 (volume.restrict (Ioo 0 T)) →
      ∀ (g : H10 n Ω) (h : L2 n Ω),
        ∃ (u : ℝ → H10 n Ω) (u_t : ℝ → L2 n Ω) (u_tt : ℝ → Hm1 n Ω),
          IsWeakSolution Ω T P f g h u u_t u_tt ∧
          (∀ (u' : ℝ → H10 n Ω) (u'_t : ℝ → L2 n Ω) (u'_tt : ℝ → Hm1 n Ω),
            IsWeakSolution Ω T P f g h u' u'_t u'_tt → ∀ t ∈ Icc 0 T, u' t = u t) ∧
          eLpNorm u ⊤ (volume.restrict (Ioo 0 T)) + eLpNorm u_t ⊤ (volume.restrict (Ioo 0 T)) +
              eLpNorm u_tt 2 (volume.restrict (Ioo 0 T)) ≤
            (C : ℝ≥0∞) * (eLpNorm f 2 (volume.restrict (Ioo 0 T)) + ‖g‖ₑ + ‖h‖ₑ) := by sorry

end HunterPDE.Hyperbolic
