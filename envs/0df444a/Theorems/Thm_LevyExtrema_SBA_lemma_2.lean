-- Prove2me | Theorems.Thm_LevyExtrema_SBA_lemma_2
-- name    : LevyExtrema.SBA.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:33.579987+00:00
-- url     : https://prove2.me/theorems/cb81d64c-9b21-42a6-9839-e63dd6aa9155
-- title:
--   Lemma 2 — explicit small-time bounds (4.12), (4.14) on $\mathbb E[\overline X_t^p]$ (corrected: β+ = δ when β = 0)
-- statement:
--   Let $X$ be a Lévy process with generating triplet $(\sigma^2,\nu,b)$ satisfying Assumption 2, let $T>0$, let $\delta$ be admissible and let $\beta_+$ be the corrected index of `betaPlus`. For every $t\in[0,T]$ and $p>0$:
--
--   1. if $I^p_+<\infty$, then
--   $$\mathbb E\big[\overline X_t^p\big]\le m^p_X(t)=4^{(p-1)^+}\big(C_{p,1}t^{p/\beta_+}+C_{p,2}t^{p/2}+C_{p,3}t^p+C_{p,4}t^{\min\{1,p/\beta_+\}}\big),\tag{4.12}$$
--   with the constants (4.13);
--   2. if $I^1_+<\infty$, then
--   $$\mathbb E[\overline X_t]\le|\sigma|\sqrt{\tfrac2\pi}\sqrt t+\begin{cases}(b^++I^1_+)t+2\sqrt{I^2_0}\sqrt t,&\beta_+=2,\\(b^++I^1_+)t+2T^{-1/\beta_+}\big(\sqrt{TI^{\beta_+}_0}+TI^{\beta_+}_0\big)t^{1/\beta_+},&\beta_+\in(1,2),\\\big(b_0^++\int_{(0,\infty)}x\,\nu(dx)\big)t,&\beta_+\le1.\end{cases}\tag{4.14}$$
--
--   The bound (4.12) is the analytic core of the paper: it gives the small-time order of $\mathbb E[\overline X^p_t]$ with constants explicit in $(\sigma^2,\nu,b)$, from which Corollary 3 and Theorem 2 follow.
--
--   Differences from the source:
--   - correction: β₊ = β + δ·1{I^β_0 = ∞} (4.6) → β₊ = β + δ when I^β_0 = ∞ or β = 0 (betaPlus); reason: as printed, standard Brownian motion (σ = 1, ν = 0, b = 0) satisfies every assumption and has β = 0, I^0_0 = 0 < ∞, hence β₊ = 0, and p/β₊ in (4.12), (4.13), (4.23) is undefined; with δ ∈ (0,1) the formulas are defined, the proofs use only I^{β₊}_0 < ∞, β₊ ≤ 2 and β₊ ≤ 1 when I^1_0 < ∞, and α₊, η_p are unchanged
--   - reading: "can thus pick δ ∈ (0, 2 − β), satisfying β + δ < 1 whenever β < 1" (one chosen δ) → the statement holds for every admissible δ (AdmissibleDelta Tr δ); reason: the stronger of the two readings of "pick δ"; it implies the statement for the chosen δ
--   - encoding: Lévy-measure integrals inside the constants → toReal of ℝ≥0∞ lintegrals; reason: each is finite under the hypotheses (I^1_+, I^2_0, I^{β₊}_0 for a Lévy triplet, ∫_{(0,∞)} x ν(dx) when β₊ ≤ 1, which forces I^1_0 < ∞)
--   - encoding: the three cases β₊ = 2, β₊ ∈ (1, 2), β₊ ≤ 1 of (4.14) → an if-chain on β₊ ∈ [0, 2]; reason: the cases are exhaustive and disjoint
--   - encoding: E[Z] for a nonnegative random variable Z, and bounds E[Z] ≤ c → ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal c; reason: lintegral of a nonnegative variable is its expectation (possibly ∞), so no bound holds by a junk value
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
--   - encoding: Assumption 2: P(X_t = x) = 0 for all x and for some (and hence all) t > 0 → Assumption2 P X, the form for all t > 0; reason: for a Lévy process the two forms are equivalent, as the page says (not_cpp_tfae); same instances
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Lemma 2, (4.12)–(4.14), p. 22

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_Assumption2
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_naturalDrift
import Definitions.Def_LevyExtrema_SBA_betaPlus
import Definitions.Def_LevyExtrema_SBA_Constants

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Lemma 2 — explicit small-time moments of the supremum** (corrected β₊).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Lemma 2, p. 22: "For all t ∈ [0, T]
and p > 0, the condition I^p_+ < ∞ implies (4.12) E[X̄^p_t] ≤ m^p_X(t) = 4^{(p−1)^+}
(C_{p,1}t^{p/β₊} + C_{p,2}t^{p/2} + C_{p,3}t^p + C_{p,4}t^{min{1,p/β₊}}), where the constants
{C_{p,i}} are given by (4.13) … Moreover, if I^1_+ < ∞, then (4.14) E[X̄_t] ≤ |σ|√(2/π)√t +
{(b^+ + I^1_+)t + 2√(I^2_0)√t, β₊ = 2; (b^+ + I^1_+)t + 2T^{−1/β₊}(√(TI^{β₊}_0) + TI^{β₊}_0)t^{1/β₊},
β₊ ∈ (1, 2); (b^+_0 + ∫_{(0,∞)} xν(dx))t, β₊ ≤ 1}."

For a Lévy process `X` with triplet `(σ², ν, b)` satisfying Assumption 2 (the standing assumption
of §4), a horizon `T > 0`, every admissible δ, every `p > 0` and every `t ∈ [0, T]`:
(4.12) if `I^p_+ < ∞` then `E[X̄_t^p] ≤ m^p_X(t)`; (4.14) if `I^1_+ < ∞` then the bound on `E[X̄_t]`.

**Formalization Note.** β₊ is `betaPlus Tr δ` (corrected: β₊ = δ also when β = 0, so `p/β₊` is
defined); the result is claimed for **every** admissible δ. Expectations are lintegrals of
`ofReal` (X̄_t ≥ 0 since X_0 = 0). `ℝ≥0∞` integrals enter through `toReal`; they are finite under
the stated hypotheses (`I^1_+`; `I^2_0` and `I^{β₊}_0` for a Lévy triplet; `∫_{(0,∞)} x ν(dx)`
when β₊ ≤ 1, which forces `I^1_0 < ∞`). The three cases of (4.14) are an if-chain on β₊ ∈ [0, 2]. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (Tr : Triplet) (hX : IsLevyWith P X Tr) (hA : Assumption2 P X)
    (T : ℝ≥0) (hT : 0 < T) (δ : ℝ) (hδ : AdmissibleDelta Tr δ) (p : ℝ) (hp : 0 < p)
    (t : ℝ≥0) (ht : t ≤ T) :
    (Iplus Tr p < ⊤ →
      ∫⁻ ω, ENNReal.ofReal (runSup (fun s => X s ω) t ^ p) ∂P
        ≤ ENNReal.ofReal (mpX Tr T δ p t)) ∧
    (Iplus Tr 1 < ⊤ →
      ∫⁻ ω, ENNReal.ofReal (runSup (fun s => X s ω) t) ∂P
        ≤ ENNReal.ofReal (|Tr.σ| * Real.sqrt (2 / Real.pi) * Real.sqrt (t : ℝ) +
          (if betaPlus Tr δ = 2 then
            (max Tr.γ 0 + (Iplus Tr 1).toReal) * (t : ℝ)
              + 2 * Real.sqrt ((I0 Tr 2).toReal) * Real.sqrt (t : ℝ)
          else if 1 < betaPlus Tr δ then
            (max Tr.γ 0 + (Iplus Tr 1).toReal) * (t : ℝ)
              + 2 * (T : ℝ) ^ (-(1 / betaPlus Tr δ)) *
                (Real.sqrt ((T : ℝ) * (I0 Tr (betaPlus Tr δ)).toReal)
                  + (T : ℝ) * (I0 Tr (betaPlus Tr δ)).toReal) *
                (t : ℝ) ^ (1 / betaPlus Tr δ)
          else
            (max (naturalDrift Tr) 0
              + (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal x ∂Tr.levyMeasure).toReal) * (t : ℝ)))) := by sorry

end LevyExtrema.SBA
