-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_corollary_26
-- name    : MultiCorrectPAC.Demo.corollary_26
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:39.858315+00:00
-- url     : https://prove2.me/theorems/31f0ce6b-40c0-4f4b-ae18-80218a5ab108
-- title:
--   Corollary 26 — m^full_H(ε, δ) ≤ (c/ε)(d log((d+1)(k+1)/ε) + log(2/δ)) with c = c(ℓ)
-- statement:
--   There is a constant $c>0$ depending only on $\ell$ such that, for finite $\mathcal Y$ with $k=|\mathcal Y|\ge\ell$ and every nonempty class $\mathcal H$ with $d=d^\cap_{\mathrm N}(\mathcal H)<\infty$, for all $\varepsilon,\delta\in(0,1)$
--   $$m^{\mathrm{full}}_{\mathcal H}(\varepsilon,\delta)\le\frac c\varepsilon\Big(d\log\frac{(d+1)(k+1)}{\varepsilon}+\log\frac2\delta\Big).$$
--
--   This is the realizable rate of Theorem A; it grows only logarithmically in $k$.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: |Y| = k < ∞ and ℓ ≤ k (§5.1, §7) → [Fintype Y], k = Fintype.card Y, hypothesis ℓ ≤ Fintype.card Y; reason: Lean convention
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: a constant c depending only on ℓ → ∃ c : ℝ, 0 < c placed after ∀ ℓ and before ∀ X Y H (and all ε, δ, m, d); reason: the quantifier order that makes c independent of X, Y, k, H, d, m, ε, δ
--   - encoding: m^full_H(ε, δ) ≤ (real bound) → ∃ m : ℕ, mFull H ε δ = m ∧ (m : ℝ) ≤ bound; reason: the bound is finite, so m^full is finite and compared as a real number
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 45 (PDF 47), Corollary 26

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem corollary_26 :
    ∀ ℓ : ℕ, 1 ≤ ℓ → ∃ c : ℝ, 0 < c ∧
      ∀ (X Y : Type) [Countable X] [Nonempty X] [Fintype Y], ℓ ≤ Fintype.card Y →
      ∀ H : Set (Hyp X Y), IsClass ℓ H → H.Nonempty →
      ∀ d : ℕ, natDim H = d →
      ∀ ε δ : ℝ, 0 < ε → ε < 1 → 0 < δ → δ < 1 →
        ∃ m : ℕ, mFull H ε δ = m ∧
          (m : ℝ) ≤ c / ε * ((d : ℝ) * Real.log (((d : ℝ) + 1) * ((Fintype.card Y : ℝ) + 1) / ε)
            + Real.log (2 / δ)) := by sorry

end MultiCorrectPAC.Demo
