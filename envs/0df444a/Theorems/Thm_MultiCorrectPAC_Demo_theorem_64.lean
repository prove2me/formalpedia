-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_theorem_64
-- name    : MultiCorrectPAC.Demo.theorem_64
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:34.689196+00:00
-- url     : https://prove2.me/theorems/0746b5fe-6e46-4fd5-83ec-507cd7d85ee9
-- title:
--   Theorem 64 (Theorem F(i)) — a nondegenerate, locally compatible class is agnostically learnable from one correct label iff d∩_DS(H̃) < ∞
-- statement:
--   Let $\mathcal X$ and $\mathcal Y$ be countable and let $\mathcal H\subseteq(\mathcal A\cup\{\star\})^{\mathcal X}$ be nondegenerate and locally compatible. Then
--   $$\mathcal H\text{ is agnostically PAC learnable from one correct label}\iff d^\cap_{\mathrm{DS}}(\tilde{\mathcal H})<\infty,$$
--   where $\tilde{\mathcal H}$ is the collapsed class (84), a class with $\ell=1$ over $\mathcal Y\cup\{\diamond\}$.
--
--   In the agnostic setting the intersection class no longer governs learnability; the collapsed class, an ordinary partial multiclass class, does.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: Y ∪ {⋄} with ⋄ ∉ Y; H̃ as a class with ℓ = 1 → Option Y with ⋄ = none; collapsedClass H : Set (Hyp X (Option Y)) whose defined values are singletons; reason: Lean convention; Definition 4 for H̃ is dsDim over the label type Option Y
--   - encoding: agnostic law D on X × A and a demonstrator (conditional law of y given (x, A) supported on A) → D : PMF (X × Finset Y) with AgnLaw ℓ D and κ : X × Finset Y → PMF Y with IsDemonstrator D κ; the learner sees i.i.d. pairs from demoLaw D κ; reason: Lean convention
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 83 (PDF 85), Theorem 64

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning
import Definitions.Def_MultiCorrectPAC_Demo_Dimensions

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem theorem_64 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Countable Y]
    [Nonempty Y] (H : Set (Hyp X Y)) (hH : IsClass ℓ H) (hnd : Nondegenerate H)
    (hlc : LocallyCompatible H) :
    AgnOneLearnable ℓ H ↔ dsDim (collapsedClass H) < ⊤ := by sorry

end MultiCorrectPAC.Demo
