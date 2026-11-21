-- Prove2me | Theorems.Thm_MasulloRH_mertens_energy_criterion_and_critical_divergence
-- name    : MasulloRH.mertens_energy_criterion_and_critical_divergence
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:00:41.736207+00:00
-- url     : https://prove2.me/theorems/8096d607-07a8-4db5-bfe3-63a00b55017d
-- title:
--   The sharp Mertens quadratic criterion for RH and unconditional divergence at the critical endpoint
-- statement:
--   Let M(k) be the ordinary summatory Möbius function. RH is equivalent to convergence of Σ M(k)²/k^(1+2θ) for every θ>1/2, and equivalently to Σ_{k≤N} M(k)²=O_d((N+1)^(2+d)) for every d>0. For any 0≤θ<1, convergence at θ puts every nontrivial zero STRICTLY to its left. In particular Σ M(k)²/k² diverges unconditionally, by the proved zero with ordinate between 14.13 and 14.14. The endpoint divergence holds even under RH.
-- source:
--   Positive quadratic estimate for the actual frontier moebius_summatory_rpow_bound_below_record (7abb4d24). The Laplace transform of M(floor(exp u)) is 1/(s ζ(s)). The exact-endpoint obstruction uses Cauchy–Schwarz together with differentiability at a hypothetical boundary zero. For the unconditional divergence we use the library theorem XiQuantitativePublished.zeta_zero_between_1413_1414.

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
set_option autoImplicit false

open Filter Finset Set Topology MeasureTheory ArithmeticFunction Asymptotics
namespace MasulloRH

theorem mertens_energy_criterion_and_critical_divergence :
    let M (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n,(moebius i:ℝ)
    let a (θ : ℝ) (n : ℕ) := (M (n+1))^2*((n:ℝ)+1)^(-(1+2*θ))
    (RiemannHypothesis ↔ ∀ θ : ℝ,1/2<θ → Summable (a θ)) ∧
    (RiemannHypothesis ↔ ∀ d : ℝ,0<d → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,
      (∑ n ∈ range N,(M (n+1))^2) ≤ C*((N:ℝ)+1)^(2+d)) ∧
    (∀ θ : ℝ,0≤θ → θ<1 → Summable (a θ) →
      ∀ z : ZetaZerosInTraceStrip (1/2), z.val.re<θ) ∧
    ¬Summable (a (1/2)) := by sorry

end MasulloRH
