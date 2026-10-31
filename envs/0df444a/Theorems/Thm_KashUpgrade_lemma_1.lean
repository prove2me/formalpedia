-- Prove2me | Theorems.Thm_KashUpgrade_lemma_1
-- name    : KashUpgrade.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:24:24.165576+00:00
-- url     : https://prove2.me/theorems/e85aff4b-fc76-4837-b0f6-f6842c650f81
-- title:
--   Lemma 1, p.14 — prices (13) from an optimal solution of (12) are optimal for (11)
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$. Let $d\ge2$, $c>0$, $\delta\in(0,1)$, let $j\ge1$ be an introduction, and let $n$ bound the upgrade experience of slice $j$. Let $\theta^*$ be an optimal solution of problem (12) with the constants (37)–(38), and let $x^*$ be related to $\theta^*$ by (13). Then $\mathrm{Revenue}_{[s_j,s_{j+1})}(x^*)$ equals the optimal value of (12), and
--   $$
--   \mathrm{Revenue}_{[s_j,s_{j+1})}(x')\le\mathrm{Revenue}_{[s_j,s_{j+1})}(x^*)
--   $$
--   for every real price function $x'$. So the two optimization problems (11) and (12) have equal optimal objective values.
--
--   The maximum over prices thus becomes a maximum over a monotone sequence of upgrade thresholds.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (possibly infinite) sequence of introductions and prices x_{j,m} for m ≤ min(j−1, n), with x₀ = 0 → a schedule with J : ℕ∞ and a total function x : ℕ → ℕ → ℝ read through classPrice; reason: the same policies; unused entries of x enter nothing and class 0 always costs 0
--   - encoding: (10) sums over s_j ≤ t ≤ s_{j+1}+d−2 → a sum over all t with the printed age range, and s_{j+1} = ∞ at the last introduction of a finite schedule; reason: the age range is empty outside the printed times; a finite schedule has a last slice that the printed formula needs ∞ for
--   - encoding: (37)–(38) with s_{j+1} and s_{j+i} → t′ ≥ s_j when introduction j+1 does not exist, and A^j_{j+i} = 0 when introduction j+i does not exist; reason: the source writes them only for existing introductions; a customer never reaches a class that does not exist
--   - encoding: θ unconstrained except for the order in (12) → θ in the support [0, ζ]; reason: thresholds are types; a threshold above a finite ζ has 1−F = 0 and the term value of ζ
--   - generalization: n the maximum possible customer upgrade experience → any n bounding the upgrade experience of the slice; reason: the source’s n is such a bound, and the larger indices have zero weight or unused prices
--   - generalization: there exist constants A^j_j, …, A^j_{j+n} → the explicit constants (37)–(38); reason: the proof of p.49 exhibits them and Algorithm 2 uses them; this implies the printed existence claim
--   - reading: the optimal prices for (11) and the optimal thresholds for (12) are related by (13) → every optimal θ* gives optimal prices through (13), and the optimal values agree; reason: the converse is false: for j = 2, raising x_{1,0} above s₁p* changes no customer’s behaviour, so an optimal price vector need not satisfy (13)
--   - encoding: (11) maximizes over the listed prices → the maximum is over all price functions; reason: by Observation 1 the other prices do not enter
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Lemma 1, p.14

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsUpgradeBoundAt
import Definitions.Def_KashUpgrade_sliceRevenue
import Definitions.Def_KashUpgrade_sliceWeight
import Definitions.Def_KashUpgrade_IsOptimalThreshold
import Definitions.Def_KashUpgrade_SatisfiesPriceRelations

namespace KashUpgrade

/-- **Lemma 1.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Lemma 1, p.14: with the constants `A` of (37)–(38), for every optimal solution
`θ*` of (12) and prices `x*` related to it by (13), the prices `x*` attain the maximum of (11) over
all real price functions, and the two optimal values are equal.

**Formalization Note** The printed "there exist constants" is stated with the constants the proof
exhibits. "Are related as follows" is read in the direction the proof establishes: every optimal
`θ*` gives optimal prices. The converse, that every optimal price vector satisfies (13), is false:
for `j = 2`, raising `x_{1,0}` above `s₁ p*` changes no customer's behaviour. -/
theorem lemma_1 {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) (S : Schedule) {d : ℕ} {c δ : ℝ} (hd : 2 ≤ d) (hc : 0 < c) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) {j n : ℕ} (hj : 1 ≤ j) (hjS : IsIntroduced S j) (hn : IsUpgradeBoundAt S d j n) {θ : ℕ → ℝ} (hθ : IsOptimalThreshold f ζ p c S.s (sliceWeight S d δ j) j n θ) {x : ℕ → ℕ → ℝ} (hx : SatisfiesPriceRelations S.s p c j n θ x) : sliceRevenue f S d c δ j x = thresholdObjective f c S.s (sliceWeight S d δ j) j n θ ∧ ∀ x' : ℕ → ℕ → ℝ, sliceRevenue f S d c δ j x' ≤ sliceRevenue f S d c δ j x := by sorry

end KashUpgrade
