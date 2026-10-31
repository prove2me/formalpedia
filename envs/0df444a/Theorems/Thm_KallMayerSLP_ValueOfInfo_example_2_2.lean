-- Prove2me | Theorems.Thm_KallMayerSLP_ValueOfInfo_example_2_2
-- name    : KallMayerSLP.ValueOfInfo.example_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:16:58.663003+00:00
-- url     : https://prove2.me/theorems/095c3531-4f63-400e-8b2f-697c1e3b1aba
-- title:
--   Example 2.2 — with random $T(\cdot)$, $EVPI=2>EEV-EV=0.75$
-- statement:
--   This is Example 2.2 of Kall & Mayer, Chapter 3: it shows that the bound $EVPI\le EEV-EV$ of Proposition 2.4 fails once the technology matrix is random.
--
--   Take $X=\mathbb R_+$ (first-stage constraint $x\ge0$ only), $c=2$, $W=(1,-1)$, $q=(1,0)^{\mathsf T}$, and a random pair $(T,h)$ with
--   $$
--   \mathbb P_\xi\{(T,h)=(1,2)\}=\mathbb P_\xi\{(T,h)=(3,12)\}=\tfrac12 ,
--   $$
--   so $\bar T=2$, $\bar h=7$. Then:
--
--   1. $EV=\min\{2x+y_1: 2x+y_1-y_2=7,\ x,y\ge0\}=7$, and $\hat x=7/2$ is an optimal first-stage solution of the EV problem;
--   2. $EEV=2\cdot\tfrac72+\tfrac12\cdot\tfrac32=7.75$ at $\hat x=7/2$;
--   3. $RS=7$, attained at $x^{*}=2$, where the second stage costs $0$ in the first scenario and $y^{(2)}_1=6$ in the second;
--   4. $WS=\tfrac12\cdot2+\tfrac12\cdot8=5$;
--   5. hence $EVPI=RS-WS=2>EEV-EV=0.75$.
--
--   **Formalization Note** The random vector is $\xi=(T,h)\in\mathbb R^2$ itself ($T(\xi)=\xi_1$, $h(\xi)=\xi_2$ in (2.1)), with law $\tfrac12\delta_{(1,2)}+\tfrac12\delta_{(3,12)}$; $X=\mathbb R_+$ is the first stage with no equality constraints ($m_1=0$). The value of the recourse objective at $x^{*}=2$ is written out as $c\,x^{*}+\mathbb E_\xi[Q(x^{*};\xi)]$. $7.75$ is written $31/4$.
--
--   Differences from the source:
--   - encoding: random data (T⁽ⁱ⁾, h⁽ⁱ⁾) ∈ {(1, 2), (3, 12)} with probability 1/2 each, X = ℝ₊ → ξ = (T, h) ∈ ℝ² with T(ξ) = ξ₁, h(ξ) = ξ₂ and law ½δ₍₁,₂₎ + ½δ₍₃,₁₂₎; m₁ = 0 first-stage equations and x ≥ 0; reason: the book's data written in the affine form (2.1)
--   - encoding: min and 𝔼 of values that may be ±∞; 𝔼 undefined for ∞ − ∞ (p.200) → EReal infima; expectation eExp = ∫f⁺ − ∫f⁻, and +∞ when ∫f⁺ = +∞; reason: the book's convention of p.200 (an undefined expected recourse is never chosen); the values agree with the book's wherever the book's are defined
--   - encoding: Q(x; …) := inf over y(·) ∈ Y = L² with a.s. constraints → the LP value realization by realization (secondStageValue at ξ); reason: the book uses Q pointwise (∀ ξ ∈ Ξ in the proof of Prop. 2.2)
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, Example 2.2, pp.247–248 (PDF 256–257)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_EVPI
import Definitions.Def_KallMayerSLP_ValueOfInfo_VSS
import Definitions.Def_KallMayerSLP_ValueOfInfo_IsEVOptimal

open MeasureTheory Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **Example 2.2: with random `T(·)`, `EVPI ≤ EEV − EV` fails.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, Example 2.2, pp.247–248
(PDF 256–257): "With `X = ℝ₊` let `c = 2`, `W = (1, −1)`, `q = (1, 0)ᵀ` and
`ℙ_ξ{(T⁽¹⁾, h⁽¹⁾) = (1, 2)} = ℙ_ξ{(T⁽²⁾, h⁽²⁾) = (3, 12)} = 1/2`." Then `EV = 7` with `x̂ = 7/2`,
`EEV = 7.75`, `RS = 7` (attained at `x* = 2`, with second-stage cost `0` in the first scenario and
`y₁⁽²⁾ = 6` in the second), `WS = 5`, and
`EVPI = RS − WS = 2 > EEV − EV = 0.75`.

**Formalization Note.** The random vector is `ξ = (T, h) ∈ ℝ²` itself: `T(ξ) = ξ₁`, `h(ξ) = ξ₂`
(`T = 0`, `T¹ = 1`, `T² = 0`, `h = 0`, `h¹ = 0`, `h² = 1` in (2.1)), with law
`½ δ_{(1,2)} + ½ δ_{(3,12)}`. `X = ℝ₊` is the first stage with no equality constraints (`m₁ = 0`)
and `x ≥ 0`. Coordinates are 0-based: `ξ 0 = T`, `ξ 1 = h`. -/
theorem example_2_2 :
    let μ : Measure (Fin 2 → ℝ) :=
      (1 / 2 : ENNReal) • Measure.dirac ![1, 2] + (1 / 2 : ENNReal) • Measure.dirac ![3, 12]
    let P : TwoStageSLP 2 1 0 2 1 :=
      TwoStageSLP.ofRandomTh 0 0 ![2] 0 ![!![1], 0] !![1, -1] 0 ![0, ![1]] ![1, 0]
    EV P μ = 7 ∧ IsEVOptimal P μ ![7 / 2] ∧ EEV P μ ![7 / 2] = 31 / 4 ∧
      RS P μ = 7 ∧
      ((P.c ⬝ᵥ ![2] : ℝ) : EReal) + eExp μ (fun ξ => recourse P ![2] ξ) = 7 ∧
      recourse P ![2] ![1, 2] = 0 ∧ recourse P ![2] ![3, 12] = 6 ∧
      WS P μ = 5 ∧ EVPI P μ = 2 ∧
      EVPI P μ > EEV P μ ![7 / 2] - EV P μ := by sorry

end KallMayerSLP.ValueOfInfo
