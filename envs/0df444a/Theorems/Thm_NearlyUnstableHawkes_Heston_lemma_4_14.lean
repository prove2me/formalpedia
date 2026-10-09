-- Prove2me | Theorems.Thm_NearlyUnstableHawkes_Heston_lemma_4_14
-- name    : NearlyUnstableHawkes.Heston.lemma_4_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:21.44414+00:00
-- url     : https://prove2.me/theorems/6aad3143-786d-43be-aa4c-fddc940e4319
-- title:
--   Lemma 4.14, p. 29 — ((B¹)^T, (B²)^T) → (B¹, B²), a two-dimensional Brownian motion, in law for the Skorohod topology
-- statement:
--   Under (3) and Assumptions 3 and 4, the pair of processes $((B^1)^T,(B^2)^T)$ of §4.4 converges in law, for the Skorohod topology on $[0,1]$, to $(B^1,B^2)$, where $(B^1,B^2)$ is a two-dimensional Brownian motion:
--   $$\big((B^1)^T,(B^2)^T\big)\Longrightarrow(B^1,B^2).$$
--
--   This is the joint invariance principle for the two normalized martingales built from $N^{T+}\pm N^{T-}$; it feeds the joint convergence of Lemma 4.15.
--
--   **Formalization Note** Stated as: a two-dimensional standard Brownian motion exists, and for every probability space carrying one, $B=(B^1,B^2)$, the pair converges in law to the path $(B^1_t,B^2_t)_{t\in[0,1]}$. The convergence is joint, for $\mathbb R^2$-valued paths with one time change for both coordinates. A two-dimensional standard Brownian motion is the published `EthierKurtz.IsStandardBrownian` with $d=2$ (two independent real Brownian motions with continuous paths).
-- source:
--   Jaisson and Rosenbaum, Limit theorems for nearly unstable Hawkes processes, arXiv:1310.2033v2, p. 29, Lemma 4.14

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

/-- Lemma 4.14, p. 29: `((B¹)^T, (B²)^T) → (B¹, B²)` in law for the Skorohod topology on
`[0, 1]` (one time change for the pair), where `(B¹, B²)` is a two-dimensional Brownian motion. -/
theorem lemma_4_14
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)]
    (T : ℕ → ℝ) (hTpos : ∀ n, 0 < T n) (hT : Tendsto T atTop atTop)
    (a : ℕ → ℝ) (φ₁ φ₂ : ℝ → ℝ) (m : ℝ) (hA3 : Assumption3 a φ₁ φ₂ m)
    (hA4 : Assumption4 T a φ₁ φ₂)
    (lam : ℝ) (hlam : 0 < lam) (h3 : Tendsto (fun n => T n * (1 - a n)) atTop (𝓝 lam))
    (μ : ℝ) (hμ : 0 < μ) (Np Nm : ∀ n, ℝ → Ω n → ℕ)
    (hH : ∀ n, IsHawkes2 (P n) μ (fun s => a n * φ₁ s) (fun s => a n * φ₂ s) (T n) (Np n) (Nm n)) :
    (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (B : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
        IsProbabilityMeasure P' ∧ EthierKurtz.IsStandardBrownian P' B) ∧
    ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') (B : ℝ≥0 → Ω' → EthierKurtz.SDEState 2),
      IsProbabilityMeasure P' → EthierKurtz.IsStandardBrownian P' B →
      ConvInLawSkorohod01 P
        (fun n t ω => ![brownianT (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n) 0 t ω,
          brownianT (T n) μ (a n) φ₁ φ₂ (Np n) (Nm n) 1 t ω])
        P' (fun t ω => ![B t.toNNReal ω 0, B t.toNNReal ω 1]) := by sorry

end NearlyUnstableHawkes.Heston
