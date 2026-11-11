-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_theorem_1_1
-- name    : MulticalibrationERM.Oracle.theorem_1_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:53:05.325949+00:00
-- url     : https://prove2.me/theorems/d4ce7111-d69a-4dfc-abea-8e68a90fa74b
-- title:
--   Theorem 1.1 — oracle-efficient multicalibration: Õ(d/ε³) samples and Õ(d/ε⁶) calls (randomized or, with an order, deterministic output), and the black-box lower bound
-- statement:
--   **(a) Upper bound.** There is an algorithm (Algorithm 4), fixed by the absolute constants of Appendix H, and absolute constants $C,a$ (with $\tilde O(f)\le Cf\log^a(ed/(\varepsilon\delta))$), such that for all $\varepsilon,\delta\in(0,1)$ and $d\ge1$, given a weighted ERM oracle for a class $H$ of VC dimension at most $d$ (any tie-breaking rule and any oracle randomness), on independent samples from any distribution $D$ over $X\times[0,1]$, the number of rounds $T$ of Appendix H (the smallest positive integer for which the bound of Theorem 3.8 is at most the target accuracy) exists in both modes, and the algorithm uses $\tilde O((d+\log(1/\delta))/\varepsilon^3)$ samples and $\tilde O((d+\log(1/\delta))/\varepsilon^6)$ oracle calls and with probability at least $1-\delta$ outputs a randomized predictor $\bar Q$ with $\mathrm{MC}(\bar Q)\le\varepsilon$. If $X$ carries a total order with measurable order intervals (Remark 2.7), the output can instead be a deterministic predictor $p$, with the same guarantees: $\tilde O((d+\log(1/\delta))/\varepsilon^3)$ samples, $\tilde O((d+\log(1/\delta))/\varepsilon^6)$ oracle calls, and $\mathrm{MC}(p)\le\varepsilon$ with probability at least $1-\delta$.
--
--   **(b) Lower bound** (explicit form, Corollary 3.12). For every $k\ge1$ there is $c_k>0$ such that, when $\varepsilon\in(0,c_k)$ and $\varepsilon^{-1}\log(1/\varepsilon)/c_k\le d\le\varepsilon^{-k}$, every black-box ERM learner that makes $\lfloor(d/\varepsilon)^k\rfloor$ oracle calls and outputs, for every class of VC dimension at most $d$ (every oracle, every distribution), a randomized predictor with multicalibration error at most $\varepsilon$ with probability at least $2/3$ uses more than $c_kd/(\varepsilon^3\log^5(1/\varepsilon))=\tilde\Omega(d/\varepsilon^3)$ samples. As printed, the case $k=1$ is vacuous (the $d$-window is empty); every $k>1$ gives a nonempty window for small $\varepsilon$.
--
--   Differences from the source:
--   - reading: Õ((d + log(1/δ))/ε³) samples and Õ((d + log(1/δ))/ε⁶) oracle calls → at most C·f·log^a(e d/(εδ)) with absolute C, a quantified before ε, δ, d and every instance; reason: Õ hides factors polylogarithmic in d, 1/ε, 1/δ (p. 3)
--   - reading: there is an algorithm (Algorithm 4) with parameters as in Appendix H, 'C a sufficiently large absolute constant' → ∃ absolute constants (C, C_0, C_b, C′) for which the concrete Algorithm 4 (oemcRandomized, oemcDeterministic) satisfies every clause; reason: Appendix H fixes the algorithm once the absolute constants are fixed
--   - generalization: a class H of VC dimension d, given to the algorithm through its parameters → any class of VC dimension at most d, d an input of the algorithm; reason: every class of VC dimension exactly d is an instance
--   - reading: Õ(d/ε³)-type bounds in part (b): 'When Ω̃(1/ε) ≤ d ≤ poly(1/ε) … makes poly(d/ε) oracle calls … uses Ω̃(d/ε³) samples' → the explicit form of Corollary 3.12, which the text designates as the explicit form of part (b); reason: the paper: 'Corollary 3.12 gives the explicit form'
--   - reading: a learner that succeeds for every class of VC dimension at most d → one algorithm for all input sets (a family A X with common n, query budget and seed law), success required for every X, class with IsAuditorClass H d, oracle and distribution; reason: the input set is not fixed by the statement; see Corollary 3.12
--   - generalization: success for every class of VC dimension at most d (part (b)) → success required only for measurable, pointwise-measurable classes; reason: a weaker hypothesis gives a stronger statement
--   - encoding: success with probability at least 2/3 (part (b)) → outer measure of the failure event at most 1/3; reason: equal to the probability for measurable learners
--   - encoding: a computable total order on X (Remark 2.7) → a LinearOrder on X with measurable order intervals; computability not modelled; reason: computability does not affect the statement
--   - encoding: k the degree of the polynomials → real k ≥ 1; reason: the paper does not restrict k to integers
--   - reading: 'choose T as the smallest integer for which the bound of Theorem 3.8 … is at most ε' (Appendix H, p. 56) → T := sInf {T ≥ 1 | bound ≤ ε}, with the conclusion 1 ≤ T in both modes (the set is nonempty); reason: Appendix H presupposes that such T exists; without the clause a choice of constants with an empty set gives T = sInf ∅ = 0, Q̄ ≡ 0, MC(Q̄) = 0 and zero samples and calls, which would make the randomized clause trivially true
--   - encoding: rounds t = 1, …, T and examples (X_t, Y_t) → rounds t = 0, …, T − 1 reading the examples from an i.i.d. stream (seedMeasure), with Gaussians, uniforms and oracle seeds as further independent coordinates; reason: index shift and explicit randomness; same algorithm
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 3–4, Theorem 1.1 (restated with proof pp. 35–37; Algorithm 4 p. 36; Appendix H pp. 56–57; Corollary 3.12 p. 23)

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast
import Definitions.Def_MulticalibrationERM_Oracle_SignedTests
import Definitions.Def_MulticalibrationERM_Oracle_BlackBox
import Definitions.Def_MulticalibrationERM_Oracle_OEMC

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Theorem 1.1 (pp. 3–4, restated pp. 35–37): oracle-efficient multicalibration.

(a) Upper bound. There are absolute constants — the constants `c` of Appendix H that fix
Algorithm 4 (OEMC), and `C, a` for `Õ(f) ≤ C f · log(e d/(εδ))^a` — such that for all
`ε, δ ∈ (0, 1)` and `d ≥ 1`, Algorithm 4 run with a weighted ERM oracle for any class `H` of VC
dimension at most `d` (with any tie-breaking and oracle randomness), on i.i.d. examples from any
distribution `D` over `X × [0, 1]`:
* the number of rounds `T` of Appendix H (the smallest positive integer for which the bound of
  Theorem 3.8 is at most the target accuracy) exists, in both modes, so `T ≥ 1`;
* in randomized mode uses `T = Õ((d + log(1/δ))/ε³)` samples and `T(N + L) =
  Õ((d + log(1/δ))/ε⁶)` oracle calls, and with probability at least `1 − δ` outputs the
  randomized predictor `Q̄` with `MC(Q̄) ≤ ε`;
* if `X` carries a total order whose order intervals are measurable (Remark 2.7), in deterministic
  mode uses `n_conf + T + n_part = Õ((d + log(1/δ))/ε³)` samples and `Õ((d + log(1/δ))/ε⁶)`
  oracle calls, and with probability at least `1 − δ` outputs a deterministic predictor `p` with
  `MC(p) ≤ ε`.

(b) Lower bound (in the explicit form of Corollary 3.12). For every `k ≥ 1` there is `c_k > 0`
such that for every `ε ∈ (0, c_k)` and `ε⁻¹ log(1/ε)/c_k ≤ d ≤ ε^{−k}`, a black-box ERM learner
making `⌊(d/ε)^k⌋` oracle calls that outputs, for every class of VC dimension at most `d`, every
oracle for it and every distribution, a randomized predictor with multicalibration error at most
`ε` with probability at least `2/3` uses more than `c_k d/(ε³ log⁵(1/ε))` samples. -/
theorem theorem_1_1 :
    (∃ c : OEMCConsts, ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
      ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ < 1 → ∀ d : ℕ, 1 ≤ d →
        1 ≤ (oemcParams c ε δ d).2.T ∧ 1 ≤ (oemcParams c (ε / 2) (δ / 4) d).2.T ∧
        (oemcRandomizedSamples c ε δ d : ℝ) ≤
            C * ((d + Real.log (1 / δ)) / ε ^ 3) * softLog d ε δ ^ a ∧
        (a1Calls (oemcParams c ε δ d).2 : ℝ) ≤
            C * ((d + Real.log (1 / δ)) / ε ^ 6) * softLog d ε δ ^ a ∧
        (oemcDeterministicSamples c ε δ d : ℝ) ≤
            C * ((d + Real.log (1 / δ)) / ε ^ 3) * softLog d ε δ ^ a ∧
        (a1Calls (oemcParams c (ε / 2) (δ / 4) d).2 : ℝ) ≤
            C * ((d + Real.log (1 / δ)) / ε ^ 6) * softLog d ε δ ^ a ∧
        ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)), IsAuditorClass H d →
        ∀ (D : LabeledDist X) {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
          [IsProbabilityMeasure ν] (O : ERMOracle X H 0 Ω),
          seedMeasure D ν {ω | ε < gridMC D H (oemcParams c ε δ d).1
              (oemcRandomized c ε δ d O ω)} ≤ ENNReal.ofReal δ ∧
          ∀ [LinearOrder X], OrderIntervalsMeasurable X →
            seedMeasure D ν {ω | ε < gridMC D H (oemcParams c (ε / 2) (δ / 4) d).1
                (detPred _ (oemcDeterministic c ε δ d O ω))} ≤ ENNReal.ofReal δ) ∧
    (∀ k : ℝ, 1 ≤ k → ∃ ck : ℝ, 0 < ck ∧
      ∀ ε : ℝ, 0 < ε → ε < ck → ∀ d : ℕ,
        ε⁻¹ * Real.log (1 / ε) / ck ≤ d → (d : ℝ) ≤ ε ^ (-k) →
      ∀ (n : ℕ) {Ωl : Type} [MeasurableSpace Ωl] (μl : Measure Ωl) [IsProbabilityMeasure μl]
        (A : ∀ (X : Type) [MeasurableSpace X], BBLearner X n ⌊((d : ℝ) / ε) ^ k⌋₊ Ωl),
        (∀ (X : Type) [MeasurableSpace X] (H : Set (X → Bool)), IsAuditorClass H d →
          ∀ {Ωo : Type} [MeasurableSpace Ωo] (νo : Measure Ωo) [IsProbabilityMeasure νo]
            (O : ERMOracle X H 0 Ωo) (D : LabeledDist X),
            bbFailProb (A X) μl O νo D ε ≤ 1 / 3) →
        ck * d / (ε ^ 3 * Real.log (1 / ε) ^ 5) < n) := by sorry

end MulticalibrationERM.Oracle
