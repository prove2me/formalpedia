-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_6
-- name    : HopfieldPSpin.Shattering.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:09:03.070027+00:00
-- url     : https://prove2.me/theorems/898ed93a-386b-4e88-a82a-27e4454ecf8d
-- title:
--   Lemma 4.6 — the norm event: sure for Rademacher patterns, $\mathbb P[T_n^c]\le Me^{-n\iota_L}\le e^{-n\iota_L/2}$ for Gaussian ones
-- statement:
--   Let $L=2$, $E_k=\{\|\eta^k\|_2\le L\sqrt n\}$ and $T_n=\bigcap_{k=1}^ME_k$. Under the standing assumptions ($p\ge3$, storage condition (2.2) with $\alpha>0$): these events are almost sure for Rademacher disorder, while for Gaussian disorder $\iota_L=\frac12(L^2-1-\log L^2)>0$ and, for all large $n$,
--   $$\mathbb P[E_k^c]\le e^{-n\iota_L},\qquad \mathbb P[T_n^c]\le Me^{-n\iota_L}\le e^{-n\iota_L/2}.$$
--   $T_n$ is the single high-probability event on which the truncated exponential moments are computed.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - encoding: almost sure events; 'for large $n$'; probabilities → measure of the complement is $0$ (for every $n$); `∀ᶠ n in atTop`; measures in $[0,\infty]$ compared with `ENNReal.ofReal`; reason: same statements
--   - encoding: standing storage condition (2.2) → hypothesis `StorageCondition p M α` with `0 < α` and $M=M_n$; reason: the paper's standing assumption, used for $\log M=o(n)$
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 18 (PDF 20), Lemma 4.6, (4.11)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

open MeasureTheory Filter

namespace HopfieldPSpin.Shattering

/-- Lemma 4.6 (p. 18): with `L = 2`, the norm events `E_k` and `T_n` are almost sure for
Rademacher disorder; for Gaussian disorder, `ι_L > 0` and for all large `n`,
`P[E_kᶜ] ≤ e^{−n ι_L}` and `P[T_nᶜ] ≤ M e^{−n ι_L} ≤ e^{−n ι_L / 2}` (under (2.2)). -/
theorem lemma_4_6 (p : ℕ) (hp : 3 ≤ p) (M : ℕ → ℕ) (α : ℝ) (hα : 0 < α)
    (hM : StorageCondition p M α) :
    (∀ n : ℕ, (∀ k : Fin (M n), disorderLaw n (M n) .rademacher (normEvent n (M n) k)ᶜ = 0) ∧
      disorderLaw n (M n) .rademacher (normEventAll n (M n))ᶜ = 0) ∧
    0 < iotaL ∧
    ∀ᶠ n : ℕ in atTop,
      (∀ k : Fin (M n), disorderLaw n (M n) .gaussian (normEvent n (M n) k)ᶜ ≤
        ENNReal.ofReal (Real.exp (-(n * iotaL)))) ∧
      disorderLaw n (M n) .gaussian (normEventAll n (M n))ᶜ ≤
        ENNReal.ofReal ((M n : ℝ) * Real.exp (-(n * iotaL))) ∧
      (M n : ℝ) * Real.exp (-(n * iotaL)) ≤ Real.exp (-(n * iotaL / 2)) := by sorry

end HopfieldPSpin.Shattering
