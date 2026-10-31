-- Prove2me | Theorems.Thm_LevyExtrema_SBA_corollary_3
-- name    : LevyExtrema.SBA.corollary_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:45:47.191014+00:00
-- url     : https://prove2.me/theorems/6edea7e6-0fe4-4186-a860-ebac0cbbd84d
-- title:
--   Corollary 3 — $\mathbb E[\overline X_t^p]\le C_p(X)t^{\eta_p-1}$ and $\mathbb E[(\overline X_t-X_t^+)^p]\le C^*_p(X)t^{\eta_p-1}$ (corrected: β+ = δ when β = 0)
-- statement:
--   Let $X$ be a Lévy process satisfying Assumption 2, $T>0$, $p>0$, and let $\delta$ be admissible with $\alpha_+<p$ whenever $\alpha<p$. With $C_p(X)$, $C^*_p(X)$ as in (4.23) and $\eta_p$ as in (4.22), for every $t\in[0,T]$:
--
--   1. if $I^p_+<\infty$, then $\mathbb E\big[\overline X^p_t\big]\le C_p(X)\,t^{\eta_p-1}$;
--   2. if $\min\{I^p_+,I^p_-\}<\infty$, then $\mathbb E\big[(\overline X_t-X^+_t)^p\big]\le C^*_p(X)\,t^{\eta_p-1}$.
--
--   The exponent $\eta_p-1$ is the one that Lemma 3 turns into the geometric rate $\eta_p^{-n}$ of Theorem 2.
--
--   Differences from the source:
--   - correction: β₊ = β + δ·1{I^β_0 = ∞} (4.6) → β₊ = β + δ when I^β_0 = ∞ or β = 0 (betaPlus); reason: as printed, standard Brownian motion (σ = 1, ν = 0, b = 0) satisfies every assumption and has β = 0, I^0_0 = 0 < ∞, hence β₊ = 0, and p/β₊ in (4.12), (4.13), (4.23) is undefined; with δ ∈ (0,1) the formulas are defined, the proofs use only I^{β₊}_0 < ∞, β₊ ≤ 2 and β₊ ≤ 1 when I^1_0 < ∞, and α₊, η_p are unchanged
--   - reading: "can thus pick δ ∈ (0, 2 − β), satisfying β + δ < 1 whenever β < 1" (one chosen δ) → the statement holds for every admissible δ (AdmissibleDelta Tr δ); reason: the stronger of the two readings of "pick δ"; it implies the statement for the chosen δ
--   - reading: "in the case p > α, we may assume that p > α₊ ≥ β₊" (proof of Corollary 3) → hypothesis α < p → α₊ < p on δ; reason: the constant C_p(X) depends on the chosen δ and the proof chooses δ with this property; the restriction bites only when α = β < p with I^β_0 = ∞, and such admissible δ always exist, so the statement is at least as strong as the one for the δ the proof picks
--   - encoding: C_p(−X) → CpX of negTriplet Tr (σ, reflected ν, −b) with the same δ; reason: −X has that triplet, and β, I^β_0, α are the same for X and −X
--   - encoding: E[Z] for a nonnegative random variable Z, and bounds E[Z] ≤ c → ∫⁻ ω, ENNReal.ofReal (Z ω) ∂P ≤ ENNReal.ofReal c; reason: lintegral of a nonnegative variable is its expectation (possibly ∞), so no bound holds by a junk value
--   - encoding: Lévy process X (paths in D[0,T], X_0 = 0) → IsLevyWith P X Tr: every path càdlàg and X_0 = 0 for every ω; reason: the paper's convention that paths lie in D[0,T] (p.18); a Lévy process has a càdlàg modification with X_0 = 0
--   - encoding: Assumption 2: P(X_t = x) = 0 for all x and for some (and hence all) t > 0 → Assumption2 P X, the form for all t > 0; reason: for a Lévy process the two forms are equivalent, as the page says (not_cpp_tfae); same instances
-- source:
--   González Cázares, Mijatović, Uribe Bravo, Geometrically Convergent Simulation of the Extrema of Lévy Processes, arXiv:1810.11039v3, Corollary 3, (4.23), p. 25

import Mathlib
import Definitions.Def_SingCtrlLevy_Barrier_Levy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_LevyExtrema_SBA_Assumption2
import Definitions.Def_LevyExtrema_SBA_LevyMeasureIntegrals
import Definitions.Def_LevyExtrema_SBA_betaPlus
import Definitions.Def_LevyExtrema_SBA_alpha
import Definitions.Def_LevyExtrema_SBA_eta
import Definitions.Def_LevyExtrema_SBA_Constants

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyExtrema.SBA

open SingCtrlLevy.Barrier

/-- **Corollary 3 — E[X̄_t^p] ≤ C_p(X) t^{η_p − 1}** (corrected β₊).
González Cázares, Mijatović, Uribe Bravo, arXiv:1810.11039v3, Corollary 3, p. 25: "Pick p > 0, let
{C_{p,i}} be as in Lemma 2 and define the constants C_p(X) and C*_p(X) as follows: (4.23) … Then,
if I^p_+ < ∞ (resp. min{I^p_+, I^p_−} < ∞), the inequality E[X̄^p_t] ≤ C_p(X)t^{η_p−1}
(resp. E[(X̄_t − X^+_t)^p] ≤ C*_p(X)t^{η_p−1}) holds for all t ∈ [0, T]."

For a Lévy process satisfying Assumption 2, `T > 0`, `p > 0`, every admissible δ with
`α < p → α₊ < p`, and every `t ∈ [0, T]`: if `I^p_+ < ∞` then `E[X̄_t^p] ≤ C_p(X) t^{η_p−1}`, and if
`min{I^p_+, I^p_−} < ∞` then `E[(X̄_t − X_t^+)^p] ≤ C*_p(X) t^{η_p−1}`.

**Formalization Note.** β₊ is corrected as in `betaPlus`. The hypothesis `α < p → α₊ < p` is the
proof's "in the case p > α, we may assume that p > α₊" (p. 25): it restricts δ only when
α = β < p with `I^β_0 = ∞`, and admissible δ satisfying it always exist. `C_p(−X)` is computed
from `negTriplet`. -/
theorem corollary_3 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (Tr : Triplet) (hX : IsLevyWith P X Tr) (hA : Assumption2 P X)
    (T : ℝ≥0) (hT : 0 < T) (p : ℝ) (hp : 0 < p) (δ : ℝ) (hδ : AdmissibleDelta Tr δ)
    (hδα : alpha Tr < p → alphaPlus Tr δ < p) (t : ℝ≥0) (ht : t ≤ T) :
    (Iplus Tr p < ⊤ →
      ∫⁻ ω, ENNReal.ofReal (runSup (fun s => X s ω) t ^ p) ∂P
        ≤ ENNReal.ofReal (CpX Tr T δ p * (t : ℝ) ^ (eta Tr δ p - 1))) ∧
    (min (Iplus Tr p) (Iminus Tr p) < ⊤ →
      ∫⁻ ω, ENNReal.ofReal ((runSup (fun s => X s ω) t - max (X t ω) 0) ^ p) ∂P
        ≤ ENNReal.ofReal (CpStar Tr T δ p * (t : ℝ) ^ (eta Tr δ p - 1))) := by sorry

end LevyExtrema.SBA
