-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_ineq_28
-- name    : MemSampleNGCA.Main.ineq_28
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:16.928868+00:00
-- url     : https://prove2.me/theorems/8b6f9dbd-b244-4ea9-9088-0392c41ea599
-- title:
--   §B.1, Inequality (28) — Ψ_{ℓ,v} ≤ T_q(4h)^ℓ · (1 + ℓ(Me^{−h})^q) at an informative state
-- statement:
--   In the setting of Theorem B.1, with $q\ge2$ and $h\ge1$, let $\Lambda_{\ell,v}$ be the propagated truncated likelihoods of Step 1. Fix $\ell\le N$ and a state $v$ in Case 2 of Step 5, i.e. $\int_\Theta\mathbf 1\{\Lambda_{\ell,v}(\theta)>e^h\}\,\pi(d\theta)>e^{-2h}$. Let
--   $$\Pi_{\ell,v}(\theta)=\frac{\mathbf 1\{\Lambda_{\ell,v}(\theta)>e^h\}}{\int_\Theta\mathbf 1\{\Lambda_{\ell,v}>e^h\}\,d\pi},\qquad\Psi_{\ell,v}=\sum_{v'\in\{0,1\}^B}\nu_\ell(v')\Big\{\int_\Theta\Lambda_{\ell,v'}(\theta)\Pi_{\ell,v}(\theta)\,\pi(d\theta)\Big\}^q.$$
--   Then
--   $$\Psi_{\ell,v}\le\{T_q(4h)\}^\ell\cdot\big\{1+\ell\cdot(Me^{-h})^q\big\}.$$
--
--   The potential bound controls the likelihood mass deleted by truncation at informative states. It is the step where the higher moment $T_q$ enters the proof of Theorem B.1 (proved in §B.1.3).
--
--   Differences from the source:
--   - generalization: π is the uniform measure on Θ ⊆ S^{d−1} → π is any probability measure on a measurable space Θ; reason: the proof uses only that π is a probability measure; the uniform measure is an instance
--   - encoding: a family {P_θ} with 0 ≤ dP_θ/dP_0 ≤ M → IsBoundedDensityFamily π P_0 p M; reason: as in Lemma B.2
--   - encoding: Definition 1.7 → StreamingAlg; reason: as in Lemma B.2
--   - encoding: Λ, Λ^{(h)}, Π, Ψ, T_q real → ℝ≥0∞-valued (Lam, LamTrunc, PiDist, Psi, Tq), conditional expectations as ratios over ν_{i+1}(v′), q-th powers as ℝ≥0∞ real powers, T_q a ⨆ over measurable f ∈ F_h; reason: same values (T_q(4h) ≤ M^q is finite here); the ratio is 0 exactly where the paper's terms carry weight 0
--   - encoding: ℓ an iteration index → ℓ ≤ N; reason: Λ_{ℓ,v} needs X_ℓ, which exists only for ℓ ≤ N in a run on N samples, and (28) is used for ℓ ≤ i ≤ N
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 21 (PDF 23), §B.1, Inequality (28); proof §B.1.3, pp. 23–24 (PDF 25–26)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- §B.1, Inequality (28) (p. 21, PDF 23; proved in §B.1.3, pp. 23–24): in Case 2 of Step 5
(`∫_Θ 1{Λ_{ℓ,v} > e^h} dπ > e^{−2h}`), the potential satisfies
`Ψ_{ℓ,v} ≤ T_q(4h)^ℓ · (1 + ℓ · (M e^{−h})^q)`. -/
theorem ineq_28 {Θ : Type*} [MeasurableSpace Θ] {X : Type*} [MeasurableSpace X]
    {B : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (π : Measure Θ) (P₀ : Measure X) (p : Θ → X → ℝ) (M : ℝ)
    (hF : IsBoundedDensityFamily π P₀ p M) (q h : ℝ) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (A : StreamingAlg B X Ω) (N ℓ : ℕ) (hℓ : ℓ ≤ N) (v : Fin B → Bool)
    (hcase : ENNReal.ofReal (Real.exp (-2 * h)) < truncMass A N π P₀ p h ℓ v) :
    Psi A N π P₀ p h q ℓ v ≤
      Tq π P₀ p q (4 * h) ^ ℓ * (1 + (ℓ : ℝ≥0∞) * ENNReal.ofReal ((M * Real.exp (-h)) ^ q)) := by sorry

end MemSampleNGCA.Main
