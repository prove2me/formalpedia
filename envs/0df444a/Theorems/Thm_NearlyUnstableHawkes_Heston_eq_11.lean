-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_eq_11
-- name    : NearlyUnstableHawkes.Heston.eq_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:39:07.206324+00:00
-- url     : https://prove2.me/theorems/63100f20-cbf7-4cd5-b429-95e10a85efa4
-- title:
--   (11), p. 27 — N^{T+}_t − N^{T−}_t = ∫_0^t (1 + Ψ^T(t − u))(dM^{T+}_u − dM^{T−}_u)
-- statement:
--   Fix $T>0$, $a_T\in(0,1)$, $\mu>0$ and kernels $\phi_1,\phi_2$ satisfying the kernel conditions of Assumption 3, and let $(N^{T+},N^{T-})$ be the bidimensional Hawkes process on $[0,T]$ with kernels $\phi^T_i=a_T\phi_i$ and baseline $\mu$. Let $\psi^T=\sum_{k\ge1}(\phi^T_1-\phi^T_2)^{*k}$ and $\Psi^T(x)=\int_0^x\psi^T(s)\,ds$. Then for every outcome and every $t\in[0,T]$,
--   $$N^{T+}_t-N^{T-}_t=\int_0^t\big(1+\Psi^T(t-u)\big)\big(dM^{T+}_u-dM^{T-}_u\big),$$
--   where $M^{T\pm}=N^{T\pm}-\int_0^\cdot\lambda^{T\pm}_s\,ds$.
--
--   This identity expresses the price process as a deterministic-kernel integral against the martingale difference $M^{T+}-M^{T-}$; it is the starting point of the decomposition of $P^T$ in Step 6.
--
--   **Formalization Note** The integral against $dM^{T\pm}$ is the pathwise Stieltjes integral: the sum of the integrand over the jump times of $N^{T\pm}$ in $(0,t]$ minus $\int_0^t(\text{integrand})\,\lambda^{T\pm}_u\,du$. The identity is stated for every $\omega$, since it follows from the definitions path by path.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 27, §4.4 Step 1, display (11)

import Mathlib
import Definitions.Def_NearlyUnstableHawkes_Heston_Kernel
import Definitions.Def_NearlyUnstableHawkes_Heston_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace NearlyUnstableHawkes.Heston

/-- Display (11), p. 27: for every `t ∈ [0, T]`, pathwise,
`N^{T+}_t − N^{T−}_t = ∫_0^t (1 + Ψ^T(t − u)) (dM^{T+}_u − dM^{T−}_u)`. -/
theorem eq_11
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hK : KernelAssumption3 φ₁ φ₂ m)
    (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (μ : ℝ) (hμ : 0 < μ) (T : ℝ) (hT : 0 < T)
    (Np Nm : ℝ → Ω → ℕ)
    (hH : IsHawkes2 P μ (fun s => a * φ₁ s) (fun s => a * φ₂ s) T Np Nm) :
    ∀ ω : Ω, ∀ t : ℝ, 0 ≤ t → t ≤ T →
      path Np ω t - path Nm ω t =
        intDiffM μ a φ₁ φ₂ Np Nm (fun u => 1 + PsiSigned a φ₁ φ₂ (t - u)) t ω := by sorry

end NearlyUnstableHawkes.Heston
