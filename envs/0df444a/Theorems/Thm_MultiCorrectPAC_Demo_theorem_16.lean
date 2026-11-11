-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_16
-- name    : MultiCorrectPAC.Demo.theorem_16
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:56.933331+00:00
-- url     : https://prove2.me/theorems/caacc4d8-204a-4044-b637-86b194d36800
-- title:
--   Theorem 16 (Theorem A, full-set half) — finite labels: d∩_DS < ∞ ⇔ d∩_N < ∞ ⇔ realizable ⇔ agnostic full-set learnability
-- statement:
--   Let $k=|\mathcal Y|<\infty$ and let $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$ be nonempty. The following are equivalent:
--   $$d^\cap_{\mathrm{DS}}(\mathcal H)<\infty\iff d^\cap_{\mathrm N}(\mathcal H)<\infty\iff\mathcal H\text{ realizably full-set PAC learnable}\iff\mathcal H\text{ agnostically full-set PAC learnable (benchmark (5))}.$$
--
--   With finitely many labels both dimensions characterize full-set learning, in the realizable and the agnostic setting; Theorem 41 applies this to the intersection class.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: |Y| = k < ∞ and ℓ ≤ k (§5.1, §7) → [Fintype Y], k = Fintype.card Y, hypothesis ℓ ≤ Fintype.card Y; reason: Lean convention
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: agnostic laws on X × A → D : PMF (X × Finset Y) with AgnLaw ℓ D (every set of positive probability in A); reason: Lean convention
--   - encoding: four equivalent conditions → List.TFAE of the four propositions; reason: Lean convention
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 36 (PDF 38), Theorem 16

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_16 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Fintype Y]
    (hk : ℓ ≤ Fintype.card Y) (H : Set (Hyp X Y)) (hH : IsClass ℓ H) (hne : H.Nonempty) :
    [dsDim H < ⊤, natDim H < ⊤, FullLearnable H, AgnFullLearnable ℓ H].TFAE := by sorry

end MultiCorrectPAC.Demo
