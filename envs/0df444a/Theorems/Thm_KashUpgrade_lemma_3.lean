-- Prove2me | Theorems.Thm_KashUpgrade_lemma_3
-- name    : KashUpgrade.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:09.556586+00:00
-- url     : https://prove2.me/theorems/19d5b8fb-e5f6-48fd-bc88-b1eb735e219c
-- title:
--   Lemma 3, p.18 — the largest out-of-order term is lumped with its neighbour
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$, and let $c>0$. Let the weights be nonnegative on $j+1,\dots,j+n$, with a positive interval $s_\ell-s_{\ell-1}$ at every index of positive weight. Let $\theta^*$ be an optimal solution of problem (12), and let $\mathcal L$ be a lumping contained in the lumping of $\theta^*$ such that every block $\mathcal L(j+k)$, $1\le k\le n$, has positive total weight (so that every term (20) below is defined). Let
--   $$
--   S=\{k:\exists k'\ \text{s.t.}\ 1\le k<k'\le n\wedge\theta^{j,FOC}_{\mathcal L(j+k)}>\theta^{j,FOC}_{\mathcal L(j+k')}\},
--   $$
--   and let $k^*$ be any maximizer of $\theta^{j,FOC}_{\mathcal L(j+k)}$ over $k\in S$. Then
--   $$
--   \theta^{*}_{j+k^*}=\theta^{*}_{j+k^*+1}.
--   $$
--
--   This identifies a constraint that must bind at the optimum, and it is what motivates the loop of OptimalLumping.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (9) with the infimum over θ → infimum over (0, ζ), value in [0, ∞], real value taken; reason: v is defined on the support; the end points change nothing because of the minimum with ζ and the infimum; the value is finite under Assumption 2
--   - encoding: θ unconstrained except for the order in (12) → θ in the support [0, ζ]; reason: thresholds are types; a threshold above a finite ζ has 1−F = 0 and the term value of ζ
--   - generalization: the weights of (38) → arbitrary nonnegative weights, where an index of positive weight has a positive interval; reason: the proof uses no more; the weights of (38) are of this kind
--   - encoding: (20) on every block of the statement → every block of the statement has positive total weight; reason: with nonnegative weights this is exactly the condition that the denominator of (20) is positive; it excludes only the instances where a term of the statement reads c·0/0, undefined in the source
--   - reading: the optimal lumping L*, the argmax k* → every optimal solution whose lumping contains L, and every maximizer; reason: the optimum is unique on the support for positive weights, and the argmax has ties; the universal reading is the strongest
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Lemma 3, p.18

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsOptimalThreshold
import Definitions.Def_KashUpgrade_firstOrderThreshold
import Definitions.Def_KashUpgrade_lumpBlock
import Definitions.Def_KashUpgrade_lumpingOf
import Definitions.Def_KashUpgrade_violators

namespace KashUpgrade

/-- **Lemma 3.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Lemma 3, p.18: let `θ*` be an optimal solution of (12) whose lumping contains
`L`, and let `k*` be a maximizer of `θ^{FOC}_{L(j+k)}` over
`S = {k : ∃ k', 1 ≤ k < k' ≤ n ∧ θ^{FOC}_{L(j+k)} > θ^{FOC}_{L(j+k')}}`. Then
`θ*_{j+k*} = θ*_{j+k*+1}`.

**Formalization Note** "The optimal solution" and the `argmax` are read universally: every optimal
solution and every maximizer. The set `S` of the lemma is `violators j n` applied to the first-order
thresholds. The weights are nonnegative, an index of positive weight has a positive interval, and
every block `L(j + k)`, `1 ≤ k ≤ n`, has positive total weight: these are exactly the instances where
every term (20) in `S` and `k*` is defined, and they cover the weights (38) of every slice. An index
of zero weight then lies in a block of positive weight, so `L ⊆ L*` pins its threshold, and the
optimal solution is unique as the lemma presupposes. The lemma holds for arbitrary such weights. -/
theorem lemma_3 {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) {c : ℝ} (hc : 0 < c) (s : ℕ → ℕ) (A : ℕ → ℝ) (j n : ℕ) (hA : ∀ ℓ ∈ Finset.Icc (j + 1) (j + n), 0 ≤ A ℓ ∧ (0 < A ℓ → s (ℓ - 1) < s ℓ)) {θ : ℕ → ℝ} (hθ : IsOptimalThreshold f ζ p c s A j n θ) {L : Finset ℕ} (hL : L ⊆ lumpingOf j n θ) (hB : ∀ k ∈ Finset.Icc 1 n, 0 < ∑ ℓ ∈ lumpBlock j n L (j + k), A ℓ) {k : ℕ} (hk : k ∈ violators j n (fun i => firstOrderThreshold f ζ c s A (lumpBlock j n L i))) (hmax : ∀ k₂ ∈ violators j n (fun i => firstOrderThreshold f ζ c s A (lumpBlock j n L i)), firstOrderThreshold f ζ c s A (lumpBlock j n L (j + k₂)) ≤ firstOrderThreshold f ζ c s A (lumpBlock j n L (j + k))) : θ (j + k) = θ (j + k + 1) := by sorry

end KashUpgrade
