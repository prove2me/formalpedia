-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_corollary_3_9
-- name    : MulticalibrationERM.Oracle.corollary_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:52:02.806206+00:00
-- url     : https://prove2.me/theorems/8833851a-b6ba-46af-bbf5-13f345a35b1f
-- title:
--   Corollary 3.9 — sample complexity of the randomized predictor, Hadamard (i) and cube (ii) clauses
-- statement:
--   There are absolute constants $C_K$ (the constant in $K$ and $\alpha$), $C$ and $a$, and a choice $T=T(\varepsilon,\delta,d)$ for each clause, such that, under the conditions of Theorem 3.8, for every $\varepsilon\in(0,1)$, $\delta\in(0,1]$, $d\ge1$, writing $\tilde O(f)$ for $C f\log^a(ed/(\varepsilon\delta))$:
--
--   (i) with $S=S_{\mathrm{Had}}$, $K=\lceil C_K/\varepsilon\rceil$, $\alpha=\varepsilon/(C_K\sqrt m)$ and $T=\tilde O\big((d+\log(1/\delta))/\varepsilon^3\big)$: for every class of VC dimension at most $d$, every distribution, every oracle and every $L\ge2\alpha^{-2}\log(16mT/\delta)$, $\mathrm{MC}(\bar Q)\le\varepsilon$ with probability at least $1-\delta$; with $L=\lceil2\alpha^{-2}\log(16mT/\delta)\rceil$ the algorithm makes $T(N+L)=\tilde O\big((d+\log(1/\delta))\varepsilon^{-6}\big)$ ERM calls in total;
--
--   (ii) with $S=S_{\mathrm{cube}}$, $K=\lceil C_K/\varepsilon\rceil$, $\alpha=\varepsilon/C_K$ and $T=\tilde O\big(\varepsilon^{-3}+(d+\log(1/\delta))\varepsilon^{-2}\big)$: $\mathrm{MC}(\bar Q)\le\varepsilon$ with probability at least $1-\delta$, with $N+L\le2^{C/\varepsilon}\log^a(ed/(\varepsilon\delta))$ ERM calls per round and $T(N+L)\le2^{C/\varepsilon}(d+\log(1/\delta))\log^a(ed/(\varepsilon\delta))$ in total.
--
--   Differences from the source:
--   - reading: T = Õ(f) (the number of rounds is chosen of order f up to polylogarithmic factors) → there is a choice function T(ε, δ, d) ≥ 1 with T ≤ C f log^a(ed/(εδ)), fixed before the class, the distribution and the oracle; reason: Õ hides factors polylogarithmic in d, 1/ε, 1/δ (p. 3); T may depend only on the algorithm's inputs
--   - reading: 2^{O(1/ε)} ERM calls per round and 2^{O(1/ε)}(d + log(1/δ)) in total → at most 2^{C/ε}·log^a(ed/(εδ)) per round and 2^{C/ε}(d + log(1/δ))·log^a(ed/(εδ)) in total; reason: L = ⌈2α⁻²log(16mT/δ)⌉ and T carry factors log(1/δ) and log d that 2^{O(1/ε)} alone cannot absorb; the paper's Õ convention hides them
--   - encoding: C in K = ⌈C/ε⌉, α and the Õ constants ('C denotes absolute constants that may change between occurrences') → separate absolute constants C_K (for K and α) and C, a (for Õ); reason: the paper's convention
--   - encoding: rounds t = 1, …, T and examples (X_t, Y_t) → rounds t = 0, …, T − 1 reading the examples from an i.i.d. stream (seedMeasure), with Gaussians, uniforms and oracle seeds as further independent coordinates; reason: index shift and explicit randomness; same algorithm
--   - generalization: a class of VC dimension d (standing assumption, p. 12) → any class of VC dimension at most d (with d ≥ 1); reason: every class of VC dimension exactly d is an instance
--   - encoding: auditors h : X → {−1,+1} → h : X → Bool with value pm (h x) ∈ {1, −1} (true ↦ +1); reason: relabelling of the two values; every auditor is an instance
--   - reading: the standard measurability conditions for suprema over H (p. 12) → every auditor measurable and the class pointwise measurable (a countable subclass whose sequences converge pointwise to every member); reason: the paper names no specific condition; pointwise measurability is the standard one under which the suprema are suprema over a countable class
--   - encoding: probability of the failure event → the measure applied to the failure set, i.e. its outer measure when the set is not measurable; reason: equal to the probability when the event is measurable; an outer-measure bound is never weaker
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), pp. 20–21, Corollary 3.9

import Mathlib
import Definitions.Def_NatureSLT_GrowthFunction_vcDim
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_ERM
import Definitions.Def_MulticalibrationERM_Oracle_Forecast
import Definitions.Def_MulticalibrationERM_Oracle_SignedTests

open MeasureTheory ProbabilityTheory

namespace MulticalibrationERM.Oracle

/-- Corollary 3.9 (pp. 20–21), both clauses: sample complexity of the randomized predictor of
Algorithm 1. There are absolute constants `CK` (the `C` in `K` and `α`), `C` and `a` (for `Õ`:
`Õ(f) ≤ C f · log(e d/(εδ))^a`) and a choice `T = T(ε, δ, d)` of the number of rounds such that,
under the conditions of Theorem 3.8 (`η = min{1, √(log N / T)}`, any `L ≥ 2α⁻² log(16mT/δ)`),
for `ε ∈ (0, 1)`:
(i) with `S = S_Had`, `K = ⌈CK/ε⌉`, `α = ε/(CK √m)`: `T = Õ((d + log(1/δ))/ε³)`,
`MC(Q̄) ≤ ε` with probability at least `1 − δ`, and with `L = ⌈2α⁻² log(16mT/δ)⌉` the total
number `T(N + L)` of ERM calls is `Õ((d + log(1/δ)) ε⁻⁶)`;
(ii) with `S = S_cube`, `K = ⌈CK/ε⌉`, `α = ε/CK`: `T = Õ(ε⁻³ + (d + log(1/δ)) ε⁻²)`,
`MC(Q̄) ≤ ε` with probability at least `1 − δ`, with `2^{O(1/ε)}` ERM calls per round and
`2^{O(1/ε)} (d + log(1/δ))` in total (up to the same polylogarithmic factor). -/
theorem corollary_3_9 :
    ∃ CK : ℝ, 0 < CK ∧ ∃ C : ℝ, 0 < C ∧ ∃ a : ℕ,
    ∃ Thad Tcube : ℝ → ℝ → ℕ → ℕ,
    ∀ (ε δ : ℝ), 0 < ε → ε < 1 → 0 < δ → δ ≤ 1 → ∀ d : ℕ, 1 ≤ d →
    -- (i) Hadamard tests
    (1 ≤ Thad ε δ d ∧
      (Thad ε δ d : ℝ) ≤ C * ((d + Real.log (1 / δ)) / ε ^ 3) * softLog d ε δ ^ a ∧
      ((Thad ε δ d * ((hadamardTests (⌈CK / ε⌉₊ + 1)).length +
          ⌈a1Lmin ⌈CK / ε⌉₊ (Thad ε δ d) (ε / (CK * Real.sqrt (⌈CK / ε⌉₊ + 1))) δ⌉₊) : ℕ) : ℝ) ≤
        C * ((d + Real.log (1 / δ)) / ε ^ 6) * softLog d ε δ ^ a ∧
      ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)), IsAuditorClass H d →
      ∀ (D : LabeledDist X) {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
        [IsProbabilityMeasure ν] (O : ERMOracle X H 0 Ω) (L : ℕ),
        a1Lmin ⌈CK / ε⌉₊ (Thad ε δ d) (ε / (CK * Real.sqrt (⌈CK / ε⌉₊ + 1))) δ ≤ L →
        seedMeasure D ν {ω | ε < gridMC D H ⌈CK / ε⌉₊
            (signedTestsQbar O ⌈CK / ε⌉₊
              ⟨hadamardTests (⌈CK / ε⌉₊ + 1), Thad ε δ d,
                a1Eta (hadamardTests (⌈CK / ε⌉₊ + 1)).length (Thad ε δ d), L⟩ ω)} ≤
          ENNReal.ofReal δ) ∧
    -- (ii) all sign patterns
    (1 ≤ Tcube ε δ d ∧
      (Tcube ε δ d : ℝ) ≤ C * (1 / ε ^ 3 + (d + Real.log (1 / δ)) / ε ^ 2) * softLog d ε δ ^ a ∧
      (((cubeTests (⌈CK / ε⌉₊ + 1)).length +
          ⌈a1Lmin ⌈CK / ε⌉₊ (Tcube ε δ d) (ε / CK) δ⌉₊ : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (C / ε) * softLog d ε δ ^ a ∧
      ((Tcube ε δ d * ((cubeTests (⌈CK / ε⌉₊ + 1)).length +
          ⌈a1Lmin ⌈CK / ε⌉₊ (Tcube ε δ d) (ε / CK) δ⌉₊) : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (C / ε) * (d + Real.log (1 / δ)) * softLog d ε δ ^ a ∧
      ∀ {X : Type} [MeasurableSpace X] (H : Set (X → Bool)), IsAuditorClass H d →
      ∀ (D : LabeledDist X) {Ω : Type} [MeasurableSpace Ω] (ν : Measure Ω)
        [IsProbabilityMeasure ν] (O : ERMOracle X H 0 Ω) (L : ℕ),
        a1Lmin ⌈CK / ε⌉₊ (Tcube ε δ d) (ε / CK) δ ≤ L →
        seedMeasure D ν {ω | ε < gridMC D H ⌈CK / ε⌉₊
            (signedTestsQbar O ⌈CK / ε⌉₊
              ⟨cubeTests (⌈CK / ε⌉₊ + 1), Tcube ε δ d,
                a1Eta (cubeTests (⌈CK / ε⌉₊ + 1)).length (Tcube ε δ d), L⟩ ω)} ≤
          ENNReal.ofReal δ) := by sorry

end MulticalibrationERM.Oracle
