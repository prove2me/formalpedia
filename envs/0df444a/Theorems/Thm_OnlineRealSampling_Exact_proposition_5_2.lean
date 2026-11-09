-- Prove2me | Theorems.Thm_OnlineRealSampling_Exact_proposition_5_2
-- name    : OnlineRealSampling.Exact.proposition_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:12:54.488495+00:00
-- url     : https://prove2.me/theorems/d4f57c51-8f12-4e52-bcad-5a761561d283
-- title:
--   Proposition 5.2 — invariants of Recycle
-- statement:
--   Let $F$ have a valid oracle, $1\le M\le\Delta$, $0\le Z<M$, and let a bit sequence be given on which Sample$(F,(Z,M),\Delta)$ halts with output $X$ and Recycle values $s,U^+,U^-,V$. Then
--   $$\Delta/4\le 2^sMf(X)\le\Delta,\qquad(16)$$
--   $$2^sMF(X)-2\le U^+\le 2^sMF(X),\qquad(17)$$
--   $$2^sMF(X-1)\le U^-\le 2^sMF(X-1)+2,\qquad(18)$$
--   $$V\le 2^sMQ\le V+1.\qquad(19)$$
--
--   These bounds make the recycled interval $\{U^-,\dots,U^+-1\}$ nearly fill the scaled output interval, which is what keeps the entropy loss of a step small.
--
--   Differences from the source:
--   - encoding: invariants of the call Recycle(F,(Z,M),Δ,X,(B_1,…,B_r)) → the four bounds for the values at the end of every terminating call of Sample, with X the output of IntervalSample; reason: Recycle is only called on the output of IntervalSample; it terminates exactly when f(X) > 0
-- source:
--   Draper, Harris & Saad, Online Random Sampling with Real Probabilities, STOC 2027 submission #103, preprint dated 2026-11-02 (source.pdf sha256 66aeb5c181baf97cefba69aa26d29299e888a7a86c837a71af5b77d35f11c3e1; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/103.pdf), Proposition 5.2, PDF 11 / printed 10

import Mathlib
import Definitions.Def_OnlineRealSampling_Exact_Algorithms

open MeasureTheory
open scoped ENNReal

namespace OnlineRealSampling.Exact

/-- Proposition 5.2 (invariants of Recycle). For a terminating call
`Sample(F, (Z, M), Δ)` with `1 ≤ M ≤ Δ`, output `X`, and Recycle values `s, U⁺, U⁻, V`:
(16) `Δ/4 ≤ 2^s M f(X) ≤ Δ`; (17) `2^s M F(X) - 2 ≤ U⁺ ≤ 2^s M F(X)`;
(18) `2^s M F(X-1) ≤ U⁻ ≤ 2^s M F(X-1) + 2`; (19) `V ≤ 2^s M Q ≤ V + 1`. -/
theorem proposition_5_2 (w : ℕ) (O : CDFOracle) (hO : O.Valid) (M Δ z : ℕ) (hM : 1 ≤ M)
    (hMΔ : M ≤ Δ) (hz : z < M) (ω : ℕ → Bool) (out : SampleOut)
    (hout : sampleRun w O.toOracleAccess z M Δ ω = some out) :
    (Δ : ℝ) / 4 ≤ 2 ^ out.sv * M * pmf O.F out.X ∧ 2 ^ out.sv * M * pmf O.F out.X ≤ Δ ∧
      2 ^ out.sv * M * O.F out.X - 2 ≤ out.Up ∧ (out.Up : ℝ) ≤ 2 ^ out.sv * M * O.F out.X ∧
      2 ^ out.sv * M * cdfPrev O.F out.X ≤ out.Um ∧
        (out.Um : ℝ) ≤ 2 ^ out.sv * M * cdfPrev O.F out.X + 2 ∧
      (out.V : ℝ) ≤ 2 ^ out.sv * M * Qvar M z ω ∧ 2 ^ out.sv * M * Qvar M z ω ≤ out.V + 1 := by sorry

end OnlineRealSampling.Exact
