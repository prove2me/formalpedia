-- Prove2me | Theorems.Thm_LEDPCount_lemma_2_17
-- name    : LEDPCount.lemma_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:06:13.294286+00:00
-- url     : https://prove2.me/theorems/96fcaaa7-90e6-4969-944c-0db59752e4ab
-- title:
--   Lemma 2.17 — debiased randomized response: privacy, mean $b$, variance $e^\varepsilon/(e^\varepsilon-1)^2=\Theta(1/\varepsilon^2)$
-- statement:
--   Let $\varepsilon>0$, $b\in\{0,1\}$, $X=\mathrm{RR}_\varepsilon(b)$ and $Y=(X(e^{\varepsilon}+1)-1)/(e^{\varepsilon}-1)$. Then
--   1. the map $b\mapsto Y$ is an $\varepsilon$-local randomizer;
--   2. $Y$ is integrable and $\mathbb E[Y]=b$;
--   3. $\displaystyle \mathrm{Var}[Y]=\frac{e^{\varepsilon}}{(e^{\varepsilon}-1)^2}$.
--
--   Moreover there are absolute constants $c_1,c_2>0$ with $c_1/\varepsilon^2\le e^{\varepsilon}/(e^{\varepsilon}-1)^2\le c_2/\varepsilon^2$ for every $\varepsilon\in(0,1]$, i.e. $\mathrm{Var}[Y]=\Theta(1/\varepsilon^2)$.
--
--   These are the unbiasedness and variance facts behind the accuracy analysis of LNC.
--
--   Differences from the source:
--   - encoding: a single input bit b → a vector Fin 1 → Bool in the local-randomizer clause; reason: Definition 2.14 with n = 1
--   - encoding: E[Y] = b → Y integrable and its integral equals b; reason: a Bochner integral of a non-integrable function is 0
--   - encoding: Var[Y] → evariance in ℝ≥0∞; reason: Lean convention; same value
--   - encoding: Θ(1/ε²) for ε ∈ (0, 1] → ∃ c₁ c₂ > 0 with c₁/ε² ≤ · ≤ c₂/ε² on (0, 1]; reason: the meaning of Θ
--   - reading: Var[Y] = e^ε/(e^ε − 1)² = Θ(1/ε²) for any ε ∈ (0, 1] → the variance identity for every ε > 0, the Θ clause on (0, 1]; reason: the range qualifies the Θ; the identity is the lemma's ε > 0 setting (Def. 2.15) and contains the (0, 1] case
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Lemma 2.17, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_LEDPCount_IsLocalRandomizer
import Definitions.Def_LEDPCount_rr

namespace LEDPCount

open MeasureTheory ProbabilityTheory

/-- Lemma 2.17 (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.17, PDF p.19): for `ε > 0` and a bit `b`, the debiased
estimate `Y = (X(e^ε + 1) − 1)/(e^ε − 1)` of `X = RR_ε(b)` is an ε-local randomizer, is
integrable with `E[Y] = b`, and has `Var[Y] = e^ε/(e^ε − 1)²`; moreover
`e^ε/(e^ε − 1)² = Θ(1/ε²)` for `ε ∈ (0, 1]`.

**Formalization Note** The input bit is a vector `a : Fin 1 → Bool` (Definition 2.14 with
`n = 1`) for the local-randomizer clause; the variance is `evariance` in `ℝ≥0∞`; `Θ(1/ε²)` is
two-sided with absolute constants. -/
theorem lemma_2_17 :
    (∀ ε : ℝ, 0 < ε →
      IsLocalRandomizer (fun a : Fin 1 → Bool => (rrBit ε (a 0)).map (debias ε)) ε ∧
      ∀ b : Bool,
        Integrable (fun x : ℝ => x) ((rrBit ε b).map (debias ε)) ∧
        ∫ x, x ∂((rrBit ε b).map (debias ε)) = (if b then 1 else 0) ∧
        evariance (fun x : ℝ => x) ((rrBit ε b).map (debias ε)) =
          ENNReal.ofReal (Real.exp ε / (Real.exp ε - 1) ^ 2)) ∧
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      c₁ / ε ^ 2 ≤ Real.exp ε / (Real.exp ε - 1) ^ 2 ∧
      Real.exp ε / (Real.exp ε - 1) ^ 2 ≤ c₂ / ε ^ 2 := by sorry

end LEDPCount
