-- Prove2me | Theorems.Thm_LEDPCount_lemma_2_9
-- name    : LEDPCount.lemma_2_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:05:39.430189+00:00
-- url     : https://prove2.me/theorems/2284c66b-c2f6-44d5-ade9-3f76a2022f94
-- title:
--   Lemma 2.9 — the Laplace mechanism is $\varepsilon$-DP
-- statement:
--   Let $\varepsilon>0$, $\Delta>0$, and let $f:\mathcal X\to\mathbb R^t$ have $\ell_1$-sensitivity at most $\Delta$ for a neighbouring relation $\sim$ on $\mathcal X$: $\|f(x)-f(x')\|_1\le\Delta$ whenever $x\sim x'$. Then the mechanism
--   $$
--   M(x)=f(x)+(Y_1,\dots,Y_t),\qquad Y_1,\dots,Y_t\ \text{independent}\ \mathrm{Lap}(\Delta/\varepsilon),
--   $$
--   is $\varepsilon$-differentially private.
--
--   This gives the privacy of the second round of LNC, with $\Delta=\Delta_Q$.
--
--   Differences from the source:
--   - encoding: ∥f(x) − f(x′)∥₁ → ∑ᵢ |f x i − f x' i|; reason: definition of the ℓ₁ norm
--   - encoding: Lap(Δ/ε) → the published PrivLearn.Generic.laplace (Δ/ε); reason: same density e^{−|z|/b}/(2b)
-- source:
--   Chen–Peng, The Power of Interaction in Locally Edge-Private Subgraph Counting, arXiv:2611.05038 (held version, sha256 d18032b0…), Lemma 2.9, p.16 (PDF p.18)

import Mathlib
import Definitions.Def_PrivLearn_Generic_Privacy
import Definitions.Def_ContinualCounting_IsApproxDP

namespace LEDPCount

open MeasureTheory

/-- Lemma 2.9 (Laplace Mechanism) (Chen–Peng, arXiv:2611.05038, held version sha256 d18032b0…, p.16, PDF p.18): let `ε > 0`, `Δ > 0` and
`f : 𝒳 → ℝ^t` with `ℓ₁`-sensitivity at most `Δ` for the neighbouring relation `Adj`. The
mechanism `M(x) = f(x) + (Y_1, …, Y_t)`, with `Y_i` independent `Lap(Δ/ε)`, is ε-DP.

**Formalization Note** The neighbour relation is arbitrary; ε-DP is the published
`ContinualCounting.IsApproxDP` with `δ = 0`. `Lap(b)` is the published
`PrivLearn.Generic.laplace b`; `PrivLearn.Parity.theorem_2_3` (dbe3ef54) is the case `t = 1` with
database neighbours. -/
theorem lemma_2_9 {𝒳 : Type*} (Adj : 𝒳 → 𝒳 → Prop) (t : ℕ) (f : 𝒳 → Fin t → ℝ) (ε Δ : ℝ)
    (hε : 0 < ε) (hΔ : 0 < Δ) (hf : ∀ x x', Adj x x' → ∑ i, |f x i - f x' i| ≤ Δ) :
    ContinualCounting.IsApproxDP Adj
      (fun x => (Measure.pi fun _ : Fin t => PrivLearn.Generic.laplace (Δ / ε)).map
        (fun z => f x + z)) ε 0 := by sorry

end LEDPCount
