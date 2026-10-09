-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_step6_decomposition
-- name    : NearlyUnstableHawkes.Heston.step6_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:44.471606+00:00
-- url     : https://prove2.me/theorems/f5b53fdc-6699-4e8c-8081-fe58fbc8bc57
-- title:
--   §4.4 Step 6, p. 31 — P^T = (1 + ‖φ‖₁/(1 − ‖φ‖₁))(M̄^{T+} − M̄^{T−}) − R^T − (‖φ‖₁/(1 − ‖φ‖₁) − a_T‖φ‖₁/(1 − a_T‖φ‖₁))(M̄^{T+} − M̄^{T−})
-- statement:
--   Fix $T>0$, $a_T\in(0,1)$, $\mu>0$ and kernels $\phi_1,\phi_2$ satisfying the kernel conditions of Assumption 3, and let $(N^{T+},N^{T-})$ be the bidimensional Hawkes process on $[0,T]$. Write $\|\phi\|_1=\int_0^\infty(\phi_1-\phi_2)$. Then for every outcome and every $t\in[0,1]$,
--   $$P^T_t=\Big(1+\frac{\|\phi\|_1}{1-\|\phi\|_1}\Big)\big(\overline M^{T+}_t-\overline M^{T-}_t\big)-R^T_t-\Big(\frac{\|\phi\|_1}{1-\|\phi\|_1}-\frac{a_T\|\phi\|_1}{1-a_T\|\phi\|_1}\Big)\big(\overline M^{T+}_t-\overline M^{T-}_t\big),$$
--   where $P^T_t=\frac1T(N^{T+}_{Tt}-N^{T-}_{Tt})$, $\overline M^{T\pm}_t=M^{T\pm}_{Tt}/T$ and $R^T_t=\int_0^t\int_{T(t-u)}^\infty\psi^T(s)\,ds\,d(\overline M^{T+}_u-\overline M^{T-}_u)$.
--
--   In the limit the first term carries the volatility $1/(1-\|\phi\|_1)$ of Theorem 3.1, $R^T$ vanishes (Lemma 4.16) and the coefficient of the third term tends to $0$.
--
--   **Formalization Note** $\|\phi\|_1$ is the signed integral $\int(\phi_1-\phi_2)$ (see the Kernel definition); with it the identity is exact, since $\int_0^\infty\psi^T=a_T\|\phi\|_1/(1-a_T\|\phi\|_1)$. The page prints "$a^T$" in the last denominator, a misprint of $a_T$. Integrals against $d\overline M$ are pathwise.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 31, §4.4 Step 6 ("Using (11) we write")

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Step 6, p. 31 ("Using (11) we write"): for `t ∈ [0, 1]`, pathwise, with `‖φ‖₁ = ∫_0^∞ (φ₁ − φ₂)`,
`P^T_t = (1 + ‖φ‖₁/(1 − ‖φ‖₁))(M̄^{T+}_t − M̄^{T−}_t) − R^T_t
  − (‖φ‖₁/(1 − ‖φ‖₁) − a_T‖φ‖₁/(1 − a_T‖φ‖₁))(M̄^{T+}_t − M̄^{T−}_t)`. -/
theorem step6_decomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hK : KernelAssumption3 φ₁ φ₂ m)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (μ : ℝ) (hμ : 0 < μ) (T : ℝ) (hT : 0 < T)
    (Np Nm : ℝ → Ω → ℕ)
    (hH : IsHawkes2 P μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) T Np Nm) :
    ∀ ω : Ω, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      priceProc T Np Nm t ω =
        (1 + phiMass φ₁ φ₂ / (1 - phiMass φ₁ φ₂)) * MbarDiff T μ a φ₁ φ₂ Np Nm t ω
          - remainderR T μ a φ₁ φ₂ Np Nm t ω
          - (phiMass φ₁ φ₂ / (1 - phiMass φ₁ φ₂)
              - a * phiMass φ₁ φ₂ / (1 - a * phiMass φ₁ φ₂)) * MbarDiff T μ a φ₁ φ₂ Np Nm t ω := by sorry

end NearlyUnstableHawkes.Heston
