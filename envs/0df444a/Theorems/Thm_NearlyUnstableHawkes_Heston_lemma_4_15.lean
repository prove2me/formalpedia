-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_15
-- name    : NearlyUnstableHawkes.Heston.lemma_4_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:10.726684+00:00
-- url     : https://prove2.me/theorems/21bbefc3-f505-4c31-81cc-4b06dd7739fb
-- title:
--   Lemma 4.15, p. 30 — (C^T, (B²)^T) → (C, B²) in law (Skorohod, [0,1]), C a CIR process independent of B²
-- statement:
--   Under (3) and Assumptions 3 and 4, the couple $(C^T,(B^2)^T)$, with $C^T_t=(\lambda^{T+}_{tT}+\lambda^{T-}_{tT})/T$, converges in law, for the Skorohod topology on $[0,1]$, toward $(C,B^2)$, where $B^2$ is a Brownian motion independent of $C$ and $C$ is a CIR process satisfying
--   $$C_t=\int_0^t\Big(\frac{2\mu}{\lambda}-C_s\Big)\frac{\lambda}{m}\,ds+\frac1m\int_0^t\sqrt{C_s}\,dW_s,$$
--   with $W$ another Brownian motion, independent of $B^2$.
--
--   The sum $N^{T+}+N^{T-}$ is a one-dimensional nearly unstable Hawkes process with baseline $2\mu$ and kernel $a_T(\phi_1+\phi_2)$, which explains the CIR limit; the lemma adds the joint convergence with $(B^2)^T$ needed to identify the limit of the price.
--
--   **Formalization Note** The limit pair is encoded as the strong solution $X=(C,Y)$, started at $0$, of the two-dimensional equation $dC=(\frac{2\mu}{\lambda}-C)\frac{\lambda}{m}dt+\frac1m\sqrt C\,dW$, $dY=dB^2$, driven by the two-dimensional standard Brownian motion $(W,B^2)$ (so $W$ and $B^2$ are independent and $Y=B^2$ almost surely). The statement is: a solution exists **whose coordinates $C$ and $Y$ are independent as path-valued random variables**, and for every solution on any probability space $(C^T,(B^2)^T)$ converges in law to $(C,Y)$ jointly (one time change). Independence is written into the existence part because it is a property of the limit law that adaptedness alone does not give.
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 30, Lemma 4.15

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

/-- Lemma 4.15, p. 30: `(C^T, (B²)^T)` converges in law, for the Skorohod topology on `[0, 1]`
(one time change for the pair), to `(C, B²)`, where `C_t = ∫_0^t (2μ/λ − C_s)(λ/m) ds
+ (1/m) ∫_0^t √C_s dW_s`, `(W, B²)` is a two-dimensional Brownian motion and `B²` is independent
of `C`. The pair `(C, B²)` is the solution `X` of the two-dimensional equation with drift
`cirPairDrift` and diffusion `cirPairDiff` driven by `(W, B²)`, started at `0`. -/
theorem lemma_4_15
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (W X : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
        IsProbabilityMeasure P' ∧ EthierKurtz.IsStandardBrownian P' W ∧
        EthierKurtz.SolvesBrownianSDE P' (cirPairDiff m) (cirPairDrift μ lam m) W (fun _ => 0) X ∧
        IndepFun (fun ω (t : ℝ≥0) => X t ω 0) (fun ω (t : ℝ≥0) => X t ω 1) P') ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω')
      (W X : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
      IsProbabilityMeasure P' → EthierKurtz.IsStandardBrownian P' W →
      EthierKurtz.SolvesBrownianSDE P' (cirPairDiff m) (cirPairDrift μ lam m) W (fun _ => 0) X →
      ConvInLawSkorohod01 P
        (fun n t ω => ![volProc (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n) t ω,
          brownianT (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n) 1 t ω])
        P' (fun t ω => ![X t.toNNReal ω 0, X t.toNNReal ω 1]) := by sorry

end NearlyUnstableHawkes.Heston
