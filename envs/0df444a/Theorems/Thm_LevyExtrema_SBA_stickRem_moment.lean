-- Prove2me | Theorems.Thm_LevyExtrema_SBA_stickRem_moment
-- name    : LevyExtrema.SBA.stickRem_moment
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:39:49.791471+00:00
-- url     : https://prove2.me/theorems/90eca6d8-aea5-4241-bda7-c4dc2b258105
-- title:
--   §4.3, proof of Theorem 2(a) — $\mathbb E[L_n^p]=T^p(1+p)^{-n}$ (corrected: (1+p)^{-n} for the printed (1+p)^n)
-- statement:
--   Let $(V_k)_{k\ge1}$ be i.i.d. $\mathrm U(0,1)$, $T\ge0$, and $L_n=T\prod_{k=1}^n(1-V_k)$ the remaining length of the stick-breaking process on $[0,T]$. Then for every $p>0$ and every $n\ge0$,
--
--   $$\mathbb E\big[L_n^p\big]=T^p(1+p)^{-n}.$$
--
--   This identity turns a small-time bound $\mathbb E[\overline X^p_t]\le Ct^q$ into the geometric bound of Lemma 3, and bounds of the time errors by $L_n$ into Theorem 2(a).
--
--   Differences from the source:
--   - correction: E[L^p_n] = T^p(1 + p)^n → E[L_n^p] = T^p (1 + p)^{−n}; reason: printed typo: for n = 1, p = 1, T = 1, E[L_1] = E[1 − V_1] = 1/2 ≠ 2; the proof of Lemma 3 on the same page uses E[C L^q_n] = C T^q (1 + q)^{−n}
--   - generalization: used for p ≥ 1 (Theorem 2(a)) and p = q > 0 (Lemma 3), n ∈ N, T > 0 → every p > 0, every n ≥ 0 and every T ≥ 0; reason: the source's uses are instances
--   - encoding: E[Z] for a nonnegative random variable Z, and bounds E[Z] ≤ c → ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal c; reason: lintegral of a nonnegative variable is its expectation (possibly ∞), so no bound holds by a junk value
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, §4.3, proof of Theorem 2(a), p. 25 (and proof of Lemma 3, same page)

import Mathlib
import Definitions.Def_LevyExtrema_SBA_StickBreaking

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

/-- **E[L_n^p] = T^p (1 + p)^{−n}** (corrected exponent).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, §4.3, proof of Theorem 2(a),
p. 25: "Since E[L^p_n] = T^p(1 + p)^n, the claim follows." The exponent is printed without its
minus sign; the proof of Lemma 3 on the same page uses `E[C L^q_n] = C T^q (1 + q)^{−n}`.

For a U(0,1)-iid sequence `V`, a horizon `T ≥ 0`, every `p > 0` and every `n`,
`E[L_n^p] = T^p (1 + p)^{−n}`, where `L_n = T ∏_{k<n} (1 − V_k)`.

**Formalization Note.** The expectation is a lintegral of `ofReal (L_n^p)`; `L_n ∈ [0, T]`
almost surely. `n = 0` is included (`L_0 = T`). -/
theorem stickRem_moment {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (hV : IsUniformSticks P V) (T : ℝ≥0) (p : ℝ) (hp : 0 < p) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (stickRem T V n ω ^ p) ∂P
      = ENNReal.ofReal ((T : ℝ) ^ p * (1 + p) ^ (-(n : ℝ))) := by sorry

end LevyExtrema.SBA
