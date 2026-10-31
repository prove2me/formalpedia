-- Prove2me | Theorems.Thm_LevyExtrema_SBA_stickBreaking_identDistrib
-- name    : LevyExtrema.SBA.stickBreaking_identDistrib
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:40:50.01806+00:00
-- url     : https://prove2.me/theorems/c8156257-7ac6-4f05-bc68-8bb9877b2df0
-- title:
--   (1.1) in law on any horizon: the stick-breaking series has the law of $(Y_t,\overline Y_t,\tau_t(Y))$
-- statement:
--   Let $Y$ be a Lévy process that is not compound Poisson with drift, let $t>0$, and let $(\ell_k,L_k)$ be the uniform stick-breaking process on $[0,t]$ driven by an i.i.d. $\mathrm U(0,1)$ sequence independent of $Y$. Then the series
--
--   $$\sum_{k=1}^\infty\Big(Y_{L_{k-1}}-Y_{L_k},\ (Y_{L_{k-1}}-Y_{L_k})^+,\ \ell_k\cdot\mathbb 1_{\{Y_{L_{k-1}}-Y_{L_k}>0\}}\Big)$$
--
--   converges almost surely, and its sum has the same law as $(Y_t,\overline Y_t,\tau_t(Y))$.
--
--   This is the stick-breaking representation (1.1) in law, for an arbitrary deterministic horizon. The proof of Theorem 1 applies it on the random interval $[0,L_n]$, conditionally on $L_n$, to identify the law of the error of the SBA.
--
--   Differences from the source:
--   - reading: "identity (1.1) applied to the interval [0, L_n] (instead of [0, T]), together with the independence of Y and ℓ" → (1.1) in law for every deterministic horizon t > 0 and sticks independent of Y; reason: the fact the sentence uses, stated before conditioning on L_n
--   - encoding: Σ_{k=1}^∞ of the summands → a.s. summability plus tsum over 0-based k; reason: Lean's stickSummand t Y V k is the paper's (k+1)-th summand; the summability clause rules out the junk value of tsum
--   - encoding: X is not compound Poisson with drift → ¬ IsCPPWithDrift Tr, i.e. ¬(σ = 0 ∧ ν(ℝ) < ∞); reason: a Lévy process is compound Poisson with drift exactly when σ = 0 and ν is finite; same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, (1.1), p. 2, as applied in §4.2, proof of Theorem 1, p. 19

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_supTime
import Definitions.Def_LevyExtrema_SBA_IsCPPWithDrift
import Definitions.Def_LevyExtrema_SBA_StickBreaking
import Definitions.Def_LevyExtrema_SBA_stickSummand

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **The stick-breaking representation (1.1) in law, on any horizon.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, (1.1), p. 2, as applied in the
proof of Theorem 1, §4.2, p. 19: "identity (1.1) applied to the interval [0, L_n] (instead of
[0, T]), together with the independence of Y and ℓ, yields the first equality in law in (1.4)".

Let `Y` be a Lévy process with triplet `Tr`, not compound Poisson with drift, `V` a U(0,1)-iid
sequence independent of the path of `Y`, and `t > 0`. Then the series of the summands
`(Y_{L_{k−1}} − Y_{L_k}, (Y_{L_{k−1}} − Y_{L_k})^+, ℓ_k 1{Y_{L_{k−1}} − Y_{L_k} > 0})` of the
stick-breaking of `[0, t]` converges almost surely, and its sum has the law of
`(Y_t, Ȳ_t, τ_t(Y))`.

**Formalization Note.** Lean's sticks are 0-based (`stickSummand t Y V k` is the paper's
(k+1)-th summand). The sum is `tsum`, preceded by the almost-sure summability clause, so the
junk value of a non-summable series plays no role. -/
theorem stickBreaking_identDistrib {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (Tr : Triplet)
    (hY : IsLevyWith P Y Tr) (hcpp : ¬ IsCPPWithDrift Tr) (hV : IsUniformSticks P V)
    (hind : IndepFun (fun ω => fun s => Y s ω) (fun ω => fun k => V k ω) P)
    (t : ℝ≥0) (ht : 0 < t) :
    (∀ᵐ ω ∂P, Summable (fun k => stickSummand t Y V k ω)) ∧
    IdentDistrib
      (fun ω => (Y t ω, runSup (fun s => Y s ω) t, ((supTime (fun s => Y s ω) t : ℝ≥0) : ℝ)))
      (fun ω => ∑' k, stickSummand t Y V k ω) P P := by sorry

end LevyExtrema.SBA
