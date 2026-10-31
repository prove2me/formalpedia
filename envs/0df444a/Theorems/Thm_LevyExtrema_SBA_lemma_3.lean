-- Prove2me | Theorems.Thm_LevyExtrema_SBA_lemma_3
-- name    : LevyExtrema.SBA.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:42:13.33255+00:00
-- url     : https://prove2.me/theorems/89fa50aa-8368-4959-ad04-195fdecb88b3
-- title:
--   Lemma 3 — a small-time bound $Ct^q$ gives $\mathbb E[\Delta_n^p]\le CT^q(1+q)^{-n}$
-- statement:
--   Let $X$ be a Lévy process satisfying Assumption 2, let $(X,\ell,Y)$ be a stick-breaking coupling on $[0,T]$ with errors $\Delta_n,\Delta^{SB}_n$, and let $C,q,p>0$.
--
--   1. If $\mathbb E[\overline X^p_t]\le Ct^q$ for all $t\in[0,T]$, then $\mathbb E[\Delta_n^p]\le CT^q(1+q)^{-n}$ for all $n\ge1$.
--   2. If $\mathbb E[(\overline X_t-X^+_t)^p]\le Ct^q$ for all $t\in[0,T]$, then $\mathbb E[(\Delta^{SB}_n)^p]\le CT^q(1+q)^{-n}$ for all $n\ge1$.
--
--   The lemma is the bridge from small-time moments of the supremum to the geometric decay of the SBA error: by Theorem 1 the error is the supremum of $Y$ over $[0,L_n]$, and $\mathbb E[L_n^q]=T^q(1+q)^{-n}$.
--
--   Differences from the source:
--   - generalization: Δ_n and Δ^SB_n "as in Theorem 1" (the coupling of Subsection 4.1) → the errors of any IsSBCoupling; reason: the proof uses only Theorem 1, which holds for every such coupling; the §4.1 coupling, with Y continued after T by an independent copy, is one (exists_sbCoupling)
--   - encoding: n ∈ N; (1 + q)^{−n} → 1 ≤ n; Real.rpow with exponent −n; reason: notation only
--   - encoding: E[Z] for a nonnegative random variable Z, and bounds E[Z] ≤ c → ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal c; reason: lintegral of a nonnegative variable is its expectation (possibly ∞), so no bound holds by a junk value
--   - encoding: Assumption 2: P(X_t = x) = 0 for all x and for some (and hence all) t > 0 → Assumption2 P X, the form for all t > 0; reason: for a Lévy process the two forms are equivalent, as the page says (not_cpp_tfae); same instances
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr, through IsSBCoupling: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Lemma 3, p. 25

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_Assumption2
import Definitions.Def_LevyExtrema_SBA_IsSBCoupling
import Definitions.Def_LevyExtrema_SBA_SBAErrors

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Lemma 3 — from a small-time moment bound to a geometric bound.**
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Lemma 3, p. 25: "Let X be Lévy
process satisfying 2 and let Δ_n and Δ^SB_n be as in Theorem 1. If E[X̄^p_t] ≤ Ct^q
(resp. E[(X̄_t − X^+_t)^p] ≤ Ct^q) for some C, q, p > 0 and all t ∈ [0, T], then
E[Δ^p_n] ≤ CT^q(1 + q)^{−n} (resp. E[(Δ^SB_n)^p] ≤ CT^q(1 + q)^{−n}) for all n ∈ N."

For a stick-breaking coupling `(X, ℓ, Y)` on `[0, T]` with `X` satisfying Assumption 2, and
`C, q, p > 0`: (i) if `E[X̄_t^p] ≤ C t^q` on `[0, T]` then `E[Δ_n^p] ≤ C T^q (1 + q)^{−n}` for all
`n ≥ 1`; (ii) the same with `(X̄_t − X_t^+)^p` and `(Δ^SB_n)^p`.

**Formalization Note.** "Δ_n and Δ^SB_n as in Theorem 1" are the errors of an `IsSBCoupling`.
"Satisfying 2" is Assumption 2 (`Assumption2 P X`). Expectations are lintegrals of `ofReal`;
`(1 + q)^{−n}` is `Real.rpow` with exponent `−n`. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : ℝ≥0 → Ω → ℝ) (V : ℕ → Ω → ℝ) (Tr : Triplet) (T : ℝ≥0)
    (hcoup : IsSBCoupling P X Y V Tr T) (hA : Assumption2 P X)
    (C q p : ℝ) (hC : 0 < C) (hq : 0 < q) (hp : 0 < p) :
    ((∀ t : ℝ≥0, t ≤ T →
        ∫⁻ ω, ENNReal.ofReal (runSup (fun s => X s ω) t ^ p) ∂P
          ≤ ENNReal.ofReal (C * (t : ℝ) ^ q)) →
      ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSup T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (C * (T : ℝ) ^ q * (1 + q) ^ (-(n : ℝ)))) ∧
    ((∀ t : ℝ≥0, t ≤ T →
        ∫⁻ ω, ENNReal.ofReal ((runSup (fun s => X s ω) t - max (X t ω) 0) ^ p) ∂P
          ≤ ENNReal.ofReal (C * (t : ℝ) ^ q)) →
      ∀ n : ℕ, 1 ≤ n →
        ∫⁻ ω, ENNReal.ofReal (errSupSB T X Y V n ω ^ p) ∂P
          ≤ ENNReal.ofReal (C * (T : ℝ) ^ q * (1 + q) ^ (-(n : ℝ)))) := by sorry

end LevyExtrema.SBA
