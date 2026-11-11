-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_3
-- name    : HopfieldPSpin.Shattering.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:47.693744+00:00
-- url     : https://prove2.me/theorems/eb125c29-d485-4499-afcf-4cacbb68a1fc
-- title:
--   Lemma 4.3 — $\mathbb E e^{\gamma nR^2}\le(1-2\gamma)^{-1/2}$ for a normalized Rademacher sum
-- statement:
--   Let $\epsilon_1,\dots,\epsilon_n$ be independent Rademacher signs and $R=n^{-1}\sum_{i=1}^n\epsilon_i$. For every $n\ge1$ and $0\le\gamma<1/2$,
--   $$\mathbb E\,e^{\gamma nR^2}\le(1-2\gamma)^{-1/2}.$$
--   It controls the exponential moment of the squared overlap of two independent uniform replicas in the second-moment computation of Theorem 4.10.
--
--   Differences from the source:
--   - encoding: $\mathbb E_R$ over independent Rademacher signs → lower Lebesgue integral of `ENNReal.ofReal (exp …)` against `Measure.pi` of the Rademacher law on $\mathbb R^n$, compared with `ENNReal.ofReal ((1-2γ)^(-1/2))`; reason: the same expectation of a nonnegative variable; the lower integral has no integrability side condition
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 17 (PDF 19), Lemma 4.3, (4.8)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

open MeasureTheory

namespace HopfieldPSpin.Shattering

/-- Lemma 4.3 (p. 17): for independent Rademacher signs `ϵ_1, …, ϵ_n` and
`R = n⁻¹ ∑ ϵ_i`, `E e^{γ n R²} ≤ (1 − 2γ)^{−1/2}` for `n ≥ 1` and `0 ≤ γ < 1/2`. -/
theorem lemma_4_3 (n : ℕ) (hn : 1 ≤ n) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ : γ < 1 / 2) :
    ∫⁻ z, ENNReal.ofReal (Real.exp (γ * n * ((1 / (n : ℝ)) * ∑ i, z i) ^ 2))
        ∂(Measure.pi fun _ : Fin n => rademacherMeasure) ≤
      ENNReal.ofReal ((1 - 2 * γ) ^ (-(1 / 2 : ℝ))) := by sorry

end HopfieldPSpin.Shattering
