-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_regret_eq_sum_gap_pulls
-- name    : LinParamBandits.UEFinite.regret_eq_sum_gap_pulls
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:21.267985+00:00
-- url     : https://prove2.me/theorems/db1d6bb8-92d8-48b4-96bc-f9244d8584ae
-- title:
--   Proof of Theorem 4.2 — Regret(z,T,UE) = Σ_u Δ^u(z) E[N^u(z,T) | Z = z]
-- statement:
--   Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis under Assumption 1, with a finite nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ ($r \ge 2$), run by the Uncertainty Ellipsoid policy. For every horizon $T$ and every $z \in \mathbb R^r$,
--   $$\mathrm{Regret}(z, T, \mathrm{UE}) = \sum_{u \in \mathcal U_r}\Delta^u(z)\,\mathbb E\big[N^u(z, T) \,\big|\, Z = z\big],$$
--   where $\Delta^u(z) = \max_{v \in \mathcal U_r} v'z - u'z$ is the gap of arm $u$ and $N^u(z, T)$ the number of periods among the first $T$ in which arm $u$ is played.
--
--   This regret decomposition turns the regret, a sum over periods, into a sum over arms, so that a bound on the number of pulls of each suboptimal arm becomes a regret bound.
--
--   **Formalization Note** The regret is defined as $T\max_v v'z - \mathbb E[\sum_{t\le T} U_t'z \mid Z = z]$. The identity holds for every horizon; the paper writes it inside the proof of Theorem 4.2, where $T \ge r + 1$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, proof of Theorem 4.2, p. 22, first line of the display after 'because'

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem regret_eq_sum_gap_pulls
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (T : ℕ) (z : LinParamBandits.LowerBound.Vec r) :
    Regret 𝒰 ν ψ z T =
      ∑ u ∈ h𝒰fin.toFinset, gap 𝒰 u z * ∫ h, (pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T) := by sorry

end LinParamBandits.UEFinite
