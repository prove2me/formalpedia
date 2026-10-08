-- Prove2me | Theorems.Thm_LinParamBandits_UEFinite_pull_count_bound
-- name    : LinParamBandits.UEFinite.pull_count_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T04:03:20.764896+00:00
-- url     : https://prove2.me/theorems/78d30e98-6b03-4432-a20e-9ffc6f4ce2b2
-- title:
--   App. B.3 — E[N^u(z,T) | Z = z] ≤ 6 + 4α²|𝒰_r| log T / (Δ^u(z))²
-- statement:
--   Consider the linearly parameterized bandit of Rusmevichientong and Tsitsiklis under Assumption 1, with a finite nonempty set of arms $\mathcal U_r \subset \mathbb R^r$ ($r \ge 2$), run by the Uncertainty Ellipsoid policy, with $\alpha = 4\sigma_0\kappa_0^2$. Let $N^u(z, T)$ be the number of periods among the first $T$ in which arm $u$ is played, and $\Delta^u(z) = \max_{v \in \mathcal U_r} v'z - u'z$ its gap. For every $T \ge r + 1$, $z \in \mathbb R^r$ and every arm $u$ with $\Delta^u(z) > 0$,
--   $$\mathbb E\big[N^u(z, T) \,\big|\, Z = z\big] \le 6 + \frac{4\alpha^2|\mathcal U_r|\log T}{(\Delta^u(z))^2}.$$
--
--   A suboptimal arm is thus played $O(\log T/\Delta^2)$ times in expectation, the same order as for the upper confidence bound policies of the classical multi-armed bandit; multiplying by the gap and summing over arms gives the regret bound of Theorem 4.2.
--
--   **Formalization Note** The hypothesis $\Delta^u(z) > 0$ is added: the paper states the bound for every arm, but its proof divides by $\Delta^u(z)$, and for an optimal arm ($\Delta^u(z) = 0$) the printed bound is meaningless (Lean's $x/0 = 0$ would turn it into the false claim $\mathbb E[N^u] \le 6$). The paper only uses the bound through $\Delta^u(z)\,\mathbb E[N^u]$, to which an optimal arm contributes $0$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, App. B.3, p. 40, display after 'To complete the proof of Theorem 4.2, it suffices to show that' (also stated in the proof of Theorem 4.2, p. 22)

import Mathlib
import Definitions.Def_LinParamBandits_UEFinite_Model
import Definitions.Def_LinParamBandits_UEFinite_UEPolicy

namespace LinParamBandits.UEFinite

open MeasureTheory ProbabilityTheory

theorem pull_count_bound
    (σ₀ ū lam₀ : ℝ) (hσ₀ : 0 < σ₀) (hū : 0 < ū) (hlam₀ : 0 < lam₀)
    (r : ℕ) (hr : 2 ≤ r) (𝒰 : Set (LinParamBandits.LowerBound.Vec r)) (h𝒰fin : 𝒰.Finite) (h𝒰ne : 𝒰.Nonempty)
    (ν : Kernel (LinParamBandits.LowerBound.Vec r) ℝ) (hν : IsMarkovKernel ν) (hnoise : NoiseAssumption 𝒰 ν σ₀)
    (b : Fin r → LinParamBandits.LowerBound.Vec r) (harms : ArmAssumption 𝒰 b ū lam₀)
    (ψ : LinParamBandits.UEGeneral.Policy r) (hψ : IsUE 𝒰 b σ₀ ū lam₀ ψ)
    (T : ℕ) (hT : r + 1 ≤ T) (z u : LinParamBandits.LowerBound.Vec r) (hu : u ∈ 𝒰) (hgap : 0 < gap 𝒰 u z) :
    ∫ h, (pullCount u h : ℝ) ∂(LinParamBandits.UEGeneral.histMeasure ν z ψ T) ≤
      6 + 4 * alpha σ₀ ū lam₀ ^ 2 * (𝒰.ncard : ℝ) * Real.log T / gap 𝒰 u z ^ 2 := by sorry

end LinParamBandits.UEFinite
