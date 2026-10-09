-- Prove2me | Theorems.Thm_HairerLiFBM_SemiDet_eq_3_24
-- name    : HairerLiFBM.SemiDet.eq_3_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:33.574298+00:00
-- url     : https://prove2.me/theorems/f72446ec-89a7-44f8-b8e8-18c5993b0653
-- title:
--   (3.24) — Kolmogorov inclusions between pathwise and process Hölder spaces
-- statement:
--   Fix a finite interval $[0,T]$, a process $x$ with measurable values, $p\ge1$, and $0<\zeta\le1$. The first inclusion in (3.24) says that an $L^p$-integrable pathwise $C^\zeta$ norm gives a finite process Hölder seminorm $\|x\|_{\zeta,p}$. For $\delta>0$ and $\zeta-1/p-\delta>0$, the second inclusion says that if the process has $L^p$ values and finite $\|x\|_{\zeta,p}$, then it has a modification $x'$ whose $C^{\zeta-1/p-\delta}$ norm is $L^p$-integrable:
--
--   $$L^p(\Omega,C^\zeta[0,T])\subseteq B_{\zeta,p}\subseteq L^p(\Omega,C^{\zeta-1/p-\delta}[0,T])\quad\text{up to modification in the second inclusion}.$$
--
--   This is the Kolmogorov regularity step used to pass from moment control of increments to convergence in probability in a pathwise Hölder space.
--
--   **Formalization Note** The process space is represented by its increment seminorm (3.16), with each time value in $L^p$. The paper's adaptedness requirement is immaterial for these analytic inclusions. The pathwise $C^\zeta$ norm includes both the supremum norm and Hölder seminorm.
-- source:
--   Hairer and Li, Averaging dynamics driven by fractional Brownian motion, Ann. Probab. 48(4) (2020), https://doi.org/10.1214/19-AOP1408, p. 1839, (3.24); notation p. 1829

import Mathlib
import Definitions.Def_HairerLiFBM_SemiDet_Model

namespace HairerLiFBM.SemiDet

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

/-- The Kolmogorov inclusions (3.24), p. 1839, with the usual modification in the second. -/
theorem eq_3_24 :
    ∀ (d : ℕ) (ζ p δ T : ℝ), 0 < d → 0 < ζ → ζ ≤ 1 →
      1 ≤ p → 0 < δ → 0 < ζ - 1 / p - δ → 0 < T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (x : ℝ → Ω → E d),
        (∀ t ∈ Set.Icc 0 T, Measurable (x t)) →
        ((∫⁻ ω,
          (supNorm (Set.Icc 0 T) (fun t => x t ω) +
            holderSemi ζ (Set.Icc 0 T) (fun t => x t ω)) ^ p ∂P) < ⊤ →
          procHolder ζ (ENNReal.ofReal p) T x P < ⊤) ∧
        ((∀ t ∈ Set.Icc 0 T, MemLp (x t) (ENNReal.ofReal p) P) →
          procHolder ζ (ENNReal.ofReal p) T x P < ⊤ →
          ∃ x' : ℝ → Ω → E d,
            (∀ t ∈ Set.Icc 0 T, x' t =ᵐ[P] x t) ∧
            (∫⁻ ω,
              (supNorm (Set.Icc 0 T) (fun t => x' t ω) +
                holderSemi (ζ - 1 / p - δ) (Set.Icc 0 T) (fun t => x' t ω)) ^ p ∂P) < ⊤) := by sorry

end HairerLiFBM.SemiDet
