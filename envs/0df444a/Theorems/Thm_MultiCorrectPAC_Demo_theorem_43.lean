-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_43
-- name    : MultiCorrectPAC.Demo.theorem_43
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:54.205502+00:00
-- url     : https://prove2.me/theorems/7fd8c9d2-2b9e-48b5-8f2c-f7bec9660c4a
-- title:
--   Theorem 43 (Theorem C) — for ℓ ≥ 2, m^one_{H_b}(ε, 1/8) > b/(4(32ε)^ℓ), and d ≤ d∩_N(I_{ℓ+1}(H_b)) < d + (ℓ+1)^ℓ with m^one > d/(4(32(ℓ+1)ε)^ℓ)
-- statement:
--   Fix $\ell\ge2$ and let $\mathcal H_b$ be the class (59). For every $b\ge1$ and $0<\varepsilon\le1/256$,
--   $$m^{\mathrm{one}}_{\mathcal H_b}(\varepsilon,1/8)>\frac{b}{4(32\varepsilon)^\ell}.$$
--   In particular, for every integer $d\ge1$ and $b=\lceil d/(\ell+1)^\ell\rceil$,
--   $$d\le d^\cap_{\mathrm N}(\mathcal I_{\ell+1}(\mathcal H_b))<d+(\ell+1)^\ell,\qquad m^{\mathrm{one}}_{\mathcal H_b}(\varepsilon,1/8)>\frac{d}{4(32(\ell+1)\varepsilon)^\ell}.$$
--
--   The exponent $\ell$ in the upper bound (55) of Theorem 41 cannot be improved in general: one-correct-label learning can need of order $d\varepsilon^{-\ell}$ examples, while full-set learning needs of order $d/\varepsilon$.
--
--   Differences from the source:
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: X = [b] × ℕ^ℓ with ℕ = {1, 2, …}, Y = [ℓ] → Fin b × (Fin ℓ → ℕ) and Fin ℓ: coordinate values shifted by one, label i ↦ index i − 1 (classHb ℓ b); reason: a relabeling of inputs and labels; it changes no instance
--   - encoding: m^one_{H_b}(ε, 1/8) > x (m^one ∈ ℕ₀ ∪ {∞}) → ∀ m : ℕ, mOne (classHb ℓ b) ε (1/8) = m → x < m; reason: an infinite sample complexity satisfies the bound; same statement
--   - encoding: b = ⌈d/(ℓ+1)^ℓ⌉ → b = ⌈(d : ℝ)/((ℓ : ℝ)+1)^ℓ⌉₊; reason: Lean convention
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 64 (PDF 66), Theorem 43

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions
import Definitions.Def_MultiCorrectPAC_Demo_LowerBoundClass

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_43 (ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    (∀ b : ℕ, 1 ≤ b → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 256 →
      ∀ m : ℕ, mOne (classHb ℓ b) ε (1 / 8) = m → (b : ℝ) / (4 * (32 * ε) ^ ℓ) < m) ∧
    (∀ d : ℕ, 1 ≤ d → ∀ b : ℕ, b = ⌈(d : ℝ) / ((ℓ : ℝ) + 1) ^ ℓ⌉₊ →
      (d : ℕ∞) ≤ natDim (interClass (ℓ + 1) (classHb ℓ b)) ∧
      natDim (interClass (ℓ + 1) (classHb ℓ b)) < ((d + (ℓ + 1) ^ ℓ : ℕ) : ℕ∞) ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 256 →
        ∀ m : ℕ, mOne (classHb ℓ b) ε (1 / 8) = m →
          (d : ℝ) / (4 * (32 * ((ℓ : ℝ) + 1) * ε) ^ ℓ) < m) := by sorry

end MultiCorrectPAC.Demo
