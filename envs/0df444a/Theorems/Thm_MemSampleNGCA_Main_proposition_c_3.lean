-- Prove2me | Theorems.Thm_MemSampleNGCA_Main_proposition_c_3
-- name    : MemSampleNGCA.Main.proposition_c_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:42:22.65403+00:00
-- url     : https://prove2.me/theorems/d7dafab0-08b5-45f9-9fa5-c4c47f3e6154
-- title:
--   Proposition C.3 — log T_q(h) ≤ q{(Cδ)^m + 2M exp(h − δd/16)} for NGCA mixtures
-- statement:
--   Let $A$ be a probability measure on $\mathbb R$ satisfying Assumption (A1) with parameter $M$ and (A2) with parameters $C>0$ and $m$. Consider the NGCA family $\Theta=S^{d-1}$ with the uniform measure $\pi$, $P_0=N(0,I_d)$ and $dP_\theta/dP_0(x)=g_A(\theta^\top x)$, and let $T_q(h)$ be the functional (17b) for this family. For an integer $q\ge1$, $h\ge0$ and $8q/d\le\delta\le1/2$,
--   $$\log T_q(h)\le q\cdot\Big\{(C\delta)^m+2M\exp\Big(h-\frac{\delta d}{16}\Big)\Big\}.$$
--
--   This higher-moment bound for diffuse mixtures of hidden-direction distributions is the NGCA-specific input to Theorem B.1. Assumption (A2) enters through the Ornstein–Uhlenbeck operator.
--
--   Differences from the source:
--   - encoding: T_q(h) for the NGCA instance → Tq (sphereUnif d) (gammaD d) (ngcaDensity d A) q h, i.e. Θ the unit sphere with normalized volume.toSphere, P_0 = stdGaussian, p(θ, x) = g_A(⟨θ, x⟩); reason: §C.1's instance of (17b), since dP_{A,θ}/dγ_d(x) = g_A(θ^⊤x)
--   - encoding: log T_q(h) real → ENNReal.log of the ℝ≥0∞-valued T_q, compared in EReal; reason: equal whenever T_q is finite and positive, and never a junk value at 0 or ∞
--   - encoding: Assumption C.1 (A1) 0 ≤ g_A ≤ M, (A2) for 0 < ρ ≤ 1/√2 → AssumptionA1 (A ≪ γ, dA/dγ ≤ M γ-a.e.) and AssumptionA2 (for ρ ∈ [0, 1/√2], ‖U_ρ g_A‖_{L∞(γ)} as eLpNorm ∞); reason: at ρ = 0, U_0 g_A ≡ 1, so the two ranges give the same assumption
--   - encoding: finite M ≥ 1 (Assumption C.1) → not stated separately; reason: A1 implies it, since ∫ g_A dγ = 1 and g_A ≤ M
--   - generalization: m ∈ ℕ → every m : ℕ, including m = 0; reason: for m = 0 both (A2) and the bound read with (Cδ)^0 = C^0ρ^0 = 1 and the proof is unchanged; for m ≥ 1 it is the source's statement
--   - encoding: d implicit → d ≥ 1; reason: 8q/d is undefined at d = 0
-- source:
--   Pensia, Gupta, Verchand, Sharan, Vedantam, Memory-Sample Tradeoffs in High-Dimensional Statistics, STOC 2027 submission (manuscript sha256 ac94994a…), p. 25 (PDF 27), Proposition C.3; proof §C.1.1, pp. 25–27 (PDF 27–29)

import Mathlib
import Definitions.Def_MemSampleNGCA_Main_Streaming
import Definitions.Def_MemSampleNGCA_Main_NGCA
import Definitions.Def_MemSampleNGCA_Main_Framework

open MeasureTheory
open scoped ENNReal

namespace MemSampleNGCA.Main

/-- Proposition C.3 (p. 25, PDF 27): if `A` satisfies Assumptions (A1)–(A2), then for an integer
`q ≥ 1`, `h ≥ 0` and `8q/d ≤ δ ≤ 1/2`, the NGCA moment functional (17b) (with `Θ = S^{d−1}`, `π`
uniform, `P₀ = N(0, I_d)`, `P_θ = P_{A,θ}`) satisfies
`log T_q(h) ≤ q · {(Cδ)^m + 2M exp(h − δd/16)}`. -/
theorem proposition_c_3 (d m : ℕ) (C M : ℝ) (A : Measure ℝ) [IsProbabilityMeasure A]
    (hA1 : AssumptionA1 M A) (hA2 : AssumptionA2 C m A)
    (q : ℕ) (hq : 1 ≤ q) (h δ : ℝ) (hh : 0 ≤ h) (hd : 1 ≤ d)
    (hδ₁ : (8 * q : ℝ) / d ≤ δ) (hδ₂ : δ ≤ 1 / 2) :
    ENNReal.log (Tq (sphereUnif d) (gammaD d) (ngcaDensity d A) q h) ≤
      ((q * ((C * δ) ^ m + 2 * M * Real.exp (h - δ * d / 16)) : ℝ) : EReal) := by sorry

end MemSampleNGCA.Main
