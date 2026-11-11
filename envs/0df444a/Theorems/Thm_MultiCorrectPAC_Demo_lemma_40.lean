-- Prove2me | Theorems.Thm_MultiCorrectPAC_Demo_lemma_40
-- name    : MultiCorrectPAC.Demo.lemma_40
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:45:53.231199+00:00
-- url     : https://prove2.me/theorems/75047427-9861-47d1-9331-71ef19da70da
-- title:
--   Lemma 40 — confidence amplification: expected loss ε/[32(ℓ+1)²] with n examples gives m^one_H(ε, δ) ≤ n⌈24(ℓ+1) log(2/δ)⌉
-- statement:
--   Let $\varepsilon,\delta\in(0,1)$. Suppose that a one-correct-label learner for $\mathcal H$ uses $n$ examples and outputs a randomized prediction rule $\hat p$ with $\mathbb E[L_{P,h^\star}(\hat p)]\le\varepsilon/[32(\ell+1)^2]$ for every $h^\star\in\mathcal H$, every $P$ with $P(\operatorname{supp}(h^\star))=1$ and every law $\mathcal D$ with marginal $P$ compatible with $h^\star$. Then
--   $$m^{\mathrm{one}}_{\mathcal H}(\varepsilon,\delta)\le n\big\lceil24(\ell+1)\log(2/\delta)\big\rceil.$$
--
--   It converts the expected-loss guarantees of Theorems 39 and 41(a) into PAC sample-complexity bounds with a multiplicative $\log(2/\delta)$.
--
--   Differences from the source:
--   - encoding: h : X → A ∪ {⋆}, a class H ⊆ (A ∪ {⋆})^X with A = {A ⊆ Y : 1 ≤ |A| ≤ ℓ} → Hyp X Y = X → Option (Finset Y) (none = ⋆), with the hypothesis IsClass ℓ H (every defined value is a nonempty finset of at most ℓ labels); reason: Lean convention; exactly the same classes
--   - encoding: standing assumptions (§5.1): X and Y nonempty countable with discrete σ-algebras, ℓ ≥ 1 → [Countable X] [Nonempty X] [Countable Y] [Nonempty Y] (Fintype Y where Y is finite) and hℓ : 1 ≤ ℓ; reason: the standing assumptions of §5.1 made explicit
--   - encoding: dimensions and sample complexities in ℕ₀ ∪ {∞}; "d < ∞" → values in ℕ∞ (⨆ resp. ⨅ over ℕ, ⊤ = ∞); "d = d∩(·) < ∞" as a natural number d with dim = d; reason: Lean convention; no junk values (⨆ ∅ = 0, ⨅ ∅ = ⊤ = ∞)
--   - encoding: distributions on the countable spaces X, X × Y; probability over m i.i.d. examples and the seed ω ∼ Unif([0,1]); errors (3) → PMFs; the probability of an event is ∑' σ, (∏ᵢ D(σᵢ)) · volume {ω ∈ unitInterval | event}; errors are values in ℝ≥0∞ and ε enters as ENNReal.ofReal ε; 'with probability ≥ 1 − δ' is stated as failure probability ≤ δ; reason: the product law on a countable sample space, written out; same numbers
--   - reading: a learner is any function of the observations and the seed ω ∼ Unif([0,1]) (and of ε, δ) → Learner / RandLearner: a map (Fin m → Z) → unitInterval → X → Y (resp. → PMF Y) that is measurable in the seed; reason: the paper's "probability over the seed" presupposes that the events are measurable; unchanged otherwise
--   - encoding: every P with P(supp(h⋆)) = 1 and every law D on X × Y with marginal P and Pr_{(x,y)∼D}[y ∈ h⋆(x)] = 1 → every D : PMF (X × Y) with Compatible h⋆ D, and P := D.map Prod.fst; reason: compatibility forces P(supp(h⋆)) = 1, so these are the same pairs (P, D)
--   - encoding: ⌈·⌉ bounds on sample complexity → m(ε, δ) ≤ ((⌈x⌉₊ : ℕ) : ℕ∞); reason: Nat.ceil equals ⌈x⌉ for the positive arguments that occur
--   - encoding: "a one-correct-label learner … outputs a randomized prediction rule p̂ with E[L] ≤ …" → A : RandLearner (X × Y) X Y n with ∀ h ∈ H, ∀ D, Compatible h D → oneExpLoss D h A ≤ ENNReal.ofReal (ε/(32(ℓ+1)²)); reason: Lean convention
--   - generalization: when Y is finite, k = |Y| and ℓ ≤ k (§5.1, p. 25) → [Countable Y] [Nonempty Y] only; a finite Y with |Y| < ℓ is not excluded; reason: ℓ enters only as a bound on the sizes of correct-label sets, which is how the paper's own argument uses it (Remark 54, p. 76, views a class with a larger ℓ); on every Y the paper allows the statement is the paper's
-- source:
--   Hanneke, Mansouri, Pour, Shaeiri, Wang, PAC Learning with Multiple Correct Answers, STOC 2027 submission (manuscript sha256 2844bd34…), p. 60 (PDF 62), Lemma 40

import Mathlib
import Definitions.Def_MultiCorrectPAC_Demo_Hypotheses
import Definitions.Def_MultiCorrectPAC_Demo_Learning

open scoped ENNReal

namespace MultiCorrectPAC.Demo

theorem lemma_40 (ℓ : ℕ) (hℓ : 1 ≤ ℓ) {X Y : Type*} [Countable X] [Nonempty X] [Countable Y]
    [Nonempty Y] (H : Set (Hyp X Y)) (hH : IsClass ℓ H) (ε δ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (n : ℕ) (A : RandLearner (X × Y) X Y n)
    (hA : ∀ h ∈ H, ∀ D : PMF (X × Y), Compatible h D →
      oneExpLoss D h A ≤ ENNReal.ofReal (ε / (32 * ((ℓ : ℝ) + 1) ^ 2))) :
    mOne H ε δ ≤ ((n * ⌈24 * ((ℓ : ℝ) + 1) * Real.log (2 / δ)⌉₊ : ℕ) : ℕ∞) := by sorry

end MultiCorrectPAC.Demo
