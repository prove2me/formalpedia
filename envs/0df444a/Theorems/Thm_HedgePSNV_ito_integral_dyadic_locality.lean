-- Prove2me | Theorems.Thm_HedgePSNV_ito_integral_dyadic_locality
-- name    : HedgePSNV.ito_integral_dyadic_locality
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-07T16:02:44.497805+00:00
-- url     : https://prove2.me/theorems/d6d5ee20-c3f9-4f34-beab-74addec9ec78
-- title:
--   Locality of the Itô integral on dyadic grids
-- statement:
--   For continuous adapted $H,H'$ with Itô integrals $J,J'$ and a set $E$ on which $H=H'$ at all dyadic points $i s/2^N$, $$J_s=J'_s\quad\text{a.s. on }E.$$
--
--   Role: identifies two integral versions in the terminal representation of $Z_T-1$.
-- source:
--   Karatzas-Shreve, Brownian Motion and Stochastic Calculus, 2nd ed., Springer GTM 113 (1991), https://doi.org/10.1007/978-1-4612-0949-2, Chapter 3, Section 3.2.B (properties of the stochastic integral, locality); proof of Theorem 1(ii), Section EC.7.3, pp. ec27-ec43

import Mathlib
import Definitions.Def_HedgePSNV_Hedging
import Definitions.Def_HedgePSNV_Model
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_completedBrownianPast
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral

set_option autoImplicit false

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped NNReal

namespace HedgePSNV

theorem ito_integral_dyadic_locality {Ω : Type*} {d : ℕ} [MeasurableSpace Ω] {P : Measure Ω} {W : ℝ≥0 → Ω → SDEState d}
    (hW : IsStandardBrownian P W) (x₀ : SDEState d) (j : Fin d) {H H' J J' : ℝ≥0 → Ω → ℝ}
    (hHm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H s))
    (hHc : ∀ ω, Continuous fun s => H s ω)
    (hH'm : ∀ s, Measurable[completedBrownianPast P W (fun _ => x₀) s] (H' s))
    (hH'c : ∀ ω, Continuous fun s => H' s ω)
    (hJ : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H J)
    (hJ' : HasBrownianItoIntegral P (completedBrownianPast P W (fun _ => x₀))
      (fun s ω => W s ω j) H' J') (s : ℝ≥0) (E : Set Ω)
    (hE : ∀ ω ∈ E, ∀ N i : ℕ, i ≤ 2 ^ N →
      H ((i : ℝ≥0) * s / (2 : ℝ≥0) ^ N) ω = H' ((i : ℝ≥0) * s / (2 : ℝ≥0) ^ N) ω) :
    ∀ᵐ ω ∂P, ω ∈ E → J s ω = J' s ω := by sorry

end HedgePSNV
