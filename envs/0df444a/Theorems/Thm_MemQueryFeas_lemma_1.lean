-- Prove2me | Theorems.Thm_MemQueryFeas_lemma_1
-- name    : MemQueryFeas.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:40:39.533415+00:00
-- url     : https://prove2.me/theorems/c380517b-26ad-4a84-a624-982aae7777da
-- title:
--   Lemma 1 — validity of the hard instance with probability $1-e^{-d/300}$
-- statement:
--   There is $d_0$ such that for all $d\ge d_0$, $0<\varepsilon\le e^{-d}$ and $P\in[d]$ the following holds. Let $E_1,\dots,E_P$ and the versions $E^{(i)}_{v',p}$ be sampled as in Algorithm 2, and let the transform separation oracle $g$ (Algorithm 4) use, after its last leaf, a final oracle that is a valid separation oracle for $Q_{E_1,\dots,E_P}$ whatever $E_1,\dots,E_P$ are. Then with probability at least $1-e^{-d/300}$:
--   1. $Q_{E_1,\dots,E_P}$ contains a (closed) ball of radius $\varepsilon$, and
--   2. after every history, every response of $g$ to a query in the unit ball is valid for $Q_{E_1,\dots,E_P}$.
--
--   The lemma shows that the random construction is, with high probability, a legitimate feasibility instance of accuracy $\varepsilon$ with a legitimate separation oracle.
--
--   Differences from the source:
--   - reading: d sufficiently large → ∃ d₀, uniform in all other parameters; reason: the usual meaning of the phrase
--   - reading: all oracle responses by g are valid → for every history and every query in the closed unit ball, the response of g is a valid response (IsValidResp); reason: queries lie in the unit ball (p.3); validity includes answering Success exactly on Q
--   - reading: the arbitrary separation oracle of Algorithm 4, line 5 → any final oracle that is valid for Q_{E_1,…,E_P} for every value of E_1,…,E_P; reason: the oracle must be a separation oracle for the realized region
--   - encoding: the random construction of Algorithm 2 → an abstract probability space carrying E_1,…,E_P and all versions, with their conditional laws as hypotheses (IsSkeleton); reason: same joint law; the paper's probabilities are probabilities under this law
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Lemma 1, p.9 (PDF p.10)

import Mathlib
import Definitions.Def_MemQueryFeas_IsSkeleton
import Definitions.Def_MemQueryFeas_GoodEvent
import Definitions.Def_MemQueryFeas_IsValidAdaptive

open MeasureTheory

namespace MemQueryFeas

/-- **Lemma 1 (validity of the hard instance).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Lemma 1, p.9 (PDF p.10): "For `d` sufficiently
large, with probability at least `1 − e^{−d/300}`, the set `Q_{E_1,...,E_P}` contains a ball of radius
`ϵ` and all oracle responses by `g` are valid separating hyperplanes for `Q_{E_1,...,E_P}`."

There is `d₀` such that for all `d ≥ d₀`, `0 < ε ≤ e^{−d}`, depth `P ∈ [d]`, every skeleton model
(Algorithm 2) and every final oracle `fin` of Algorithm 4, line 5, that is a valid separation oracle
for `Q_{E_1,…,E_P}` whatever the `E_p`: with probability at least `1 − e^{−d/300}`, `Q_{E_1,…,E_P}`
contains a closed `ε`-ball and every response of the transform oracle `g` to a query in the unit
ball, after any history, is valid (`GoodEvent`).

**Formalization Note.** "`d` sufficiently large" is `∃ d₀`, uniform in `ε` and `P`. The standing
assumptions of §3 (`0 < ε ≤ e^{−d}`, `P ∈ [d]`) are explicit. The probability is the measure of the
event. -/
theorem lemma_1 :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ Real.exp (-(d : ℝ)) →
      ∀ P : ℕ, 1 ≤ P → P ≤ d →
      ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (ν : Measure (Op d)) (Eb : ℕ → Ω → Op d) (ch : ℕ → List ℕ → ℕ → Ω → Op d),
        IsSkeleton d ε P μ ν Eb ch →
      ∀ fin : (ℕ → Op d) → List (Vec d) → Vec d → Option (Vec d),
        (∀ Ebv : ℕ → Op d, IsValidAdaptive (Qset ε P Ebv) (fin Ebv)) →
        ENNReal.ofReal (1 - Real.exp (-(d : ℝ) / 300)) ≤
          μ {ω | GoodEvent d ε P (fun p => Eb p ω) (fun p v i => ch p v i ω)
            (fin (fun p => Eb p ω))} := by sorry

end MemQueryFeas
