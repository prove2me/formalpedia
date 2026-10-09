-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_theorem_3_13
-- name    : HairerLiFBM.SemiDet.theorem_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:18.007645+00:00
-- url     : https://prove2.me/theorems/7108459c-b4eb-4674-8e2d-4aab034bd43c
-- title:
--   Theorem 3.13 — convergence in probability of averaged Young solutions
-- statement:
--   Let $B$ be a two-sided $m$-dimensional fractional Brownian motion with Hurst index $1/2<H<1$, taken in a locally Hölder version. Fix $T>0$ and $1/2<\alpha<H-\kappa$, with $\kappa,\gamma>0$, $\kappa,\gamma\le1$, $H-\kappa>1/2$, and $H-\kappa+\gamma\alpha>1$. Let $\alpha<\zeta\le1$. Suppose each time-dependent coefficient $f_n$ is $\zeta$-Hölder in time with values in bounded $C^2$, and the autonomous coefficient $\bar f$ lies in bounded $C^2$. If $f_n-\bar f$ tends to zero in the negative Hölder norm (3.12) on $[0,T]$, let $x^n$ and $x$ be the Young solutions from the same $x_0$ of
--
--   $$dx^n_t=f_n(t,x^n_t)\,dB_t,\qquad dx_t=\bar f(x_t)\,dB_t.$$
--
--   Then for every $\varepsilon>0$,
--
--   $$P\left(\|x^n-x\|_{C^\alpha[0,T]}>\varepsilon\right)\longrightarrow0.$$
--
--   This is the semideterministic averaging result of Section 3: negative time regularity is sufficient to control the solutions in the strong path topology in probability.
--
--   **Formalization Note** The coefficient $\bar f$ is autonomous as in equation (3.23), although the printed theorem's type suggests a time argument. Convergence of the negative Hölder norm is witnessed by bounds $K_n\to0$. The $C^\alpha$ norm is the sum of the supremum norm and homogeneous seminorm. This item covers the $dB$ equations; the final sentence of the printed theorem concerning an additional $dt$ term is recorded as deferred.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, p. 1838, Theorem 3.13 (3.23); proof pp. 1838–1839

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- Theorem 3.13, p. 1838: convergence of the Young solutions in probability in C^α. -/
theorem theorem_3_13
    (m d : ℕ) (H α κ γ ζ T : ℝ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ → Ω → E m)
    (f : ℕ → ℝ → E d → (E m →L[ℝ] E d))
    (fbar : E d → (E m →L[ℝ] E d)) (x0 : E d)
    (X : ℕ → ℝ → Ω → E d) (Xbar : ℝ → Ω → E d)
    (hm : 0 < m) (hd : 0 < d)
    (hH : 1 / 2 < H) (hH1 : H < 1)
    (hα : 1 / 2 < α) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hη : 1 / 2 < H - κ) (hηbar : 1 < H - κ + γ * α)
    (hαη : α < H - κ) (hαζ : α < ζ) (hζ : ζ ≤ 1) (hT : 0 < T)
    (hB : IsFBM m H B P) (hBholder : HasHolderPaths m H B P)
    (hf : ∀ n, InCzeta2 ζ (f n)) (hfbar : IsBC2 fbar)
    (haverage : ∃ K : ℕ → ℝ, Tendsto K atTop (𝓝 0) ∧
      ∀ n, NegHolderBound κ γ T (K n) (fun r y => f n r y - fbar y))
    (hX : ∀ n, ∀ᵐ ω ∂P,
      IsYoungSolution α T (f n) (fun t => B t ω) x0 (fun t => X n t ω))
    (hXbar : ∀ᵐ ω ∂P,
      IsYoungSolution α T (fun _ => fbar) (fun t => B t ω) x0 (fun t => Xbar t ω)) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ENNReal.ofReal ε <
        supNorm (Set.Icc 0 T) (fun t => X n t ω - Xbar t ω) +
        holderSemi α (Set.Icc 0 T) (fun t => X n t ω - Xbar t ω)})
        atTop (𝓝 (0 : ℝ≥0∞)) := by sorry

end HairerLiFBM.SemiDet
