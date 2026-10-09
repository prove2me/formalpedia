-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_theorem_3_1
-- name    : NearlyUnstableHawkes.Heston.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:21.206849+00:00
-- url     : https://prove2.me/theorems/7ade6a3f-09bc-4ecb-a407-665b98aef280
-- title:
--   Theorem 3.1, p. 14 — the Hawkes-based price P^T converges in law (Skorohod, [0,1]) to a Heston-type process with volatility (1/(1 − ‖φ‖₁))√C
-- statement:
--   Let $T=T_n\to\infty$. Let $\phi_1,\phi_2$ and $(a_T)$ satisfy Assumption 3 (nonnegative kernels with $\int_0^\infty(\phi_1+\phi_2)=1$, $\int_0^\infty s(\phi_1+\phi_2)(s)\,ds=m<\infty$, $\phi_2$ supported on a set of positive measure, $\phi_i$ differentiable with bounded integrable derivative; $0<a_T<1$, $a_T\to1$), Assumption 4 (the rescaled resolvent densities $\rho^T$ are uniformly bounded) and (3), $T(1-a_T)\to\lambda>0$. For each $T$, let $(N^{T+},N^{T-})$ be the bidimensional Hawkes process on $[0,T]$ with baseline $\mu>0$ and kernel matrix $\begin{pmatrix}\phi^T_1&\phi^T_2\\ \phi^T_2&\phi^T_1\end{pmatrix}$, $\phi^T_i=a_T\phi_i$, and let
--   $$P^T_t=\frac1T\big(N^{T+}_{Tt}-N^{T-}_{Tt}\big).$$
--   Let $\phi=\phi_1-\phi_2$. Then $(P^T_t)$ converges in law, for the Skorohod topology on $[0,1]$, toward the Heston-type process $P$ defined by
--   $$\begin{cases} dC_t=\Big(\dfrac{2\mu}{\lambda}-C_t\Big)\dfrac{\lambda}{m}\,dt+\dfrac1m\sqrt{C_t}\,dB^1_t, & C_0=0,\\[2mm] dP_t=\dfrac{1}{1-\|\phi\|_1}\sqrt{C_t}\,dB^2_t, & P_0=0,\end{cases}$$
--   with $(B^1,B^2)$ a bidimensional Brownian motion.
--
--   The price of a nearly unstable Hawkes-based microstructure model, observed over the time scale on which its stability condition is almost violated, behaves like the price in a Heston model: its variance is a CIR process.
--
--   **Formalization Note** $\|\phi\|_1$ is read as the signed integral $\int_0^\infty(\phi_1-\phi_2)$, the value the proof uses (Step 6, p. 31), which equals the $L^1$ norm when $\phi_1\ge\phi_2$; under Assumption 3 it lies in $[-1,1)$, so the volatility constant is finite. The asymptotic parameter $T$ runs along a sequence $T_n\to\infty$ (footnote 1, p. 5). The system for $(C,P)$ is encoded with the published `EthierKurtz.SolvesBrownianSDE` (strong solutions: continuous, adapted to the completed Brownian filtration, equation holding for all times a.s.) in state space $\mathbb R^2$, driven by a two-dimensional standard Brownian motion, started at $0$. "Converges toward the process defined by" is stated as: a solution exists, and for every solution on any probability space, $P^T$ converges in law to its $P$-coordinate, which also yields uniqueness of the limit law. Convergence in law for the Skorohod topology on $[0,1]$ is in coupling form (Setting). Solutions are global in time; only $[0,1]$ is used. $\sqrt{\cdot}$ is `Real.sqrt`.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 14, Theorem 3.1 (with (6), p. 14; Assumptions 3–4, pp. 13–14; (3), p. 8)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_SDEDiffusion
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SolvesBrownianSDE
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Theorem 3.1, p. 14: under (3) and Assumptions 3 and 4, the Hawkes-based price models `P^T`
converge in law, for the Skorohod topology on `[0, 1]`, to the second coordinate `P` of the
Heston-type system `dC_t = (2μ/λ − C_t)(λ/m) dt + (1/m)√C_t dB¹_t`, `C_0 = 0`,
`dP_t = (1/(1 − ‖φ‖₁))√C_t dB²_t`, `P_0 = 0`, with `(B¹, B²)` a bidimensional Brownian motion and
`‖φ‖₁ = ∫_0^∞ (φ₁ − φ₂)`. Stated as: a solution exists, and `P^T` converges to the `P`-coordinate of
every solution. -/
theorem theorem_3_1
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
        IsProbabilityMeasure P' ∧ EthierKurtz.IsStandardBrownian P' B ∧
        EthierKurtz.SolvesBrownianSDE P' (hestonDiff m φ₁ φ₂) (hestonDrift μ lam m) B
          (fun _ => 0) X) ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (B X : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
      IsProbabilityMeasure P' → EthierKurtz.IsStandardBrownian P' B →
      EthierKurtz.SolvesBrownianSDE P' (hestonDiff m φ₁ φ₂) (hestonDrift μ lam m) B
        (fun _ => 0) X →
      ConvInLawSkorohod01 P (fun n => priceProc (T n) (Np n) (Nm n))
        P' (fun t ω => X t.toNNReal ω 1) := by sorry

end NearlyUnstableHawkes.Heston
