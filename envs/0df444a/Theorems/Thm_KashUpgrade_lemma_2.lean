-- Prove2me | Theorems.Thm_KashUpgrade_lemma_2
-- name    : KashUpgrade.lemma_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:10.0663+00:00
-- url     : https://prove2.me/theorems/75b65632-1d90-4015-94e5-b935ad2043a9
-- title:
--   Lemma 2, p.18 — merging blocks keeps the first-order threshold in the middle
-- statement:
--   Let the type law satisfy Assumption 2 and let $c>0$. Let the weights be nonnegative on $j+1,\dots,j+n$, with a positive interval $s_\ell-s_{\ell-1}$ at every index of positive weight. If $\mathcal L\subseteq\mathcal L'$ are lumpings, $j+1\le i\le j+n$, and every block $\mathcal L(\iota)$, $\iota\in\mathcal L'(i)$, has positive total weight (so that every term (20) below is defined), then
--   $$
--   \min_{\iota\in\mathcal L'(i)}\theta^{j,FOC}_{\mathcal L(\iota)}\ \le\ \theta^{j,FOC}_{\mathcal L'(i)}\ \le\ \max_{\iota\in\mathcal L'(i)}\theta^{j,FOC}_{\mathcal L(\iota)} .
--   $$
--
--   When terms are lumped together, the maximizer of the new joint term lies between the maximizers of the terms that make it up.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (9) with the infimum over θ → infimum over (0, ζ), value in [0, ∞], real value taken; reason: v is defined on the support; the end points change nothing because of the minimum with ζ and the infimum; the value is finite under Assumption 2
--   - generalization: the weights of (38) → arbitrary nonnegative weights, where an index of positive weight has a positive interval; reason: the proof uses no more; the weights of (38) are of this kind
--   - encoding: (20) on every block of the statement → every block of the statement has positive total weight; reason: with nonnegative weights this is exactly the condition that the denominator of (20) is positive; it excludes only the instances where a term of the statement reads c·0/0, undefined in the source
--   - encoding: the minimum and the maximum over L′(i) → two indices ι₁, ι₂ ∈ L′(i) attaining the bounds; reason: the set is finite and nonempty, so this is the same statement
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Lemma 2, p.18

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_firstOrderThreshold
import Definitions.Def_KashUpgrade_lumpBlock

namespace KashUpgrade

/-- **Lemma 2.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Lemma 2, p.18: if `L ⊆ L'` then for every `j + 1 ≤ i ≤ j + n`,
`min_{ι ∈ L'(i)} θ^{FOC}_{L(ι)} ≤ θ^{FOC}_{L'(i)} ≤ max_{ι ∈ L'(i)} θ^{FOC}_{L(ι)}`.

**Formalization Note** The minimum and the maximum over the finite nonempty set `L'(i)` are written
as two existential indices. The weights are nonnegative, an index of positive weight has a positive
interval, and every block `L(ι)`, `ι ∈ L'(i)`, has positive total weight: these are exactly the
instances where every term (20) of the statement is defined (its denominator is positive), and
they cover the weights (38) of every slice. The lemma holds for arbitrary such weights. -/
theorem lemma_2 {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {c : ℝ} (hc : 0 < c) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ) (hA : ∀ ℓ ∈ Finset.Icc (j + 1) (j + n), 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ)) {L L' : Finset ℕ} (hL : L ⊆ L') {i : ℕ} (hi : i ∈ Finset.Icc (j + 1) (j + n)) (hB : ∀ ι ∈ lumpBlock j n L' i, 0 < ∑ ℓ ∈ lumpBlock j n L ι, A ℓ) : ∃ ι₁ ∈ lumpBlock j n L' i, ∃ ι₂ ∈ lumpBlock j n L' i, firstOrderThreshold f ζ c s A (lumpBlock j n L ι₁) ≤ firstOrderThreshold f ζ c s A (lumpBlock j n L' i) ∧ firstOrderThreshold f ζ c s A (lumpBlock j n L' i) ≤ firstOrderThreshold f ζ c s A (lumpBlock j n L ι₂) := by sorry

end KashUpgrade
