-- Prove2me | Theorems.Thm_KashUpgrade_theorem_1_discriminatoryPricing_optimal
-- name    : KashUpgrade.theorem_1_discriminatoryPricing_optimal
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:26:27.281834+00:00
-- url     : https://prove2.me/theorems/617f8a13-0319-451f-a13d-d91d0fc08dcf
-- title:
--   Theorem 1, p.19 — DiscriminatoryPricing produces optimal prices
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$. Let $d\ge2$, $c>0$, $\delta\in(0,1)$, fix a finite or infinite introduction schedule, and let $n\le d-1$ bound the upgrade experience of every slice. Then:
--
--   1. for every introduction $j\ge1$, OptimalLumping with the weights (38) has a terminating run;
--   2. for every family of terminating runs, one per introduction, the prices $x$ that DiscriminatoryPricing builds from them have a summable revenue series, and
--   $$
--   \mathrm{Revenue}(\pi(\mathbf s,x'))\le\mathrm{Revenue}(\pi(\mathbf s,x))
--   $$
--   for every real price function $x'$ with a summable revenue series.
--
--   So the algorithm solves the infinite horizon discriminatory pricing problem with fixed introduction times (8).
--
--   The maximizer chosen in each iteration of OptimalLumping is arbitrary. The result holds for every terminating run, and the comparison is over all real prices, including prices at which new customers buy older classes.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (9) with the infimum over θ → infimum over (0, ζ), value in [0, ∞], real value taken; reason: v is defined on the support; the end points change nothing because of the minimum with ζ and the infimum; the value is finite under Assumption 2
--   - encoding: (possibly infinite) sequence of introductions and prices x_{j,m} for m ≤ min(j−1, n), with x₀ = 0 → a schedule with J : ℕ∞ and a total function x : ℕ → ℕ → ℝ read through classPrice; reason: the same policies; unused entries of x enter nothing and class 0 always costs 0
--   - encoding: (37)–(38) with s_{j+1} and s_{j+i} → t′ ≥ s_j when introduction j+1 does not exist, and A^j_{j+i} = 0 when introduction j+i does not exist; reason: the source writes them only for existing introductions; a customer never reaches a class that does not exist
--   - reading: k* ← argmax_{k∈S} γ_{j+k} → every run with an arbitrary maximizer at every step that terminates, and existence of a terminating run; reason: the printed rule has ties, and for some choices the loop repeats a state forever
--   - generalization: n the maximum possible customer upgrade experience, n ≤ d − 1 → any n ≤ d − 1 bounding the upgrade experience of every slice; reason: the source’s n is such a bound, and extra indices have zero weight
--   - encoding: x*_s ∈ argmax Revenue(π(s, x_s)) → summability of the algorithm’s series, and comparison with every x′ whose series is summable; reason: Lean’s sum of a non-summable series is 0; a myopic customer pays at most θ·t, so a non-summable series diverges to −∞ and cannot win
--   - encoding: (20) and Algorithm 1 on a block of weight 0, where the update reads c·0/0 → Lean’s value 0; reason: the source leaves this undefined; these indices have zero weight and their prices enter no revenue
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Theorem 1, p.19; Algorithms 1–2, pp.19–20; (8), p.12

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsTerminalRun
import Definitions.Def_KashUpgrade_IsUpgradeBoundAt
import Definitions.Def_KashUpgrade_discriminatoryPrices
import Definitions.Def_KashUpgrade_sliceWeight
import Definitions.Def_KashUpgrade_totalRevenue

namespace KashUpgrade

/-- **Theorem 1.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Theorem 1, p.19: the DiscriminatoryPricing algorithm produces optimal prices
for the infinite horizon discriminatory pricing problem with fixed introduction times (8).

Take `d ≥ 2`, `c > 0`, `δ ∈ (0, 1)`, a type law satisfying Assumption 2, its Myerson price `p*`, any
finite or infinite schedule, and `n ≤ d - 1` bounding the upgrade experience of every slice. Then
OptimalLumping has a terminating run for every `j`. For every family of terminating runs, the prices
that DiscriminatoryPricing builds from them have a summable revenue series, and they earn at least
the revenue of every real price function whose revenue series is summable.

**Formalization Note** The `argmax` of Algorithm 1 is read as a free choice, so the theorem covers
every terminating run, and part one says that one exists. The price functions `x'` are unrestricted.
A non-summable series has `tsum = 0` in Lean, so the comparison is guarded by summability. Nothing
is lost: a myopic customer never pays more than `θ · t` in a period, so the positive part of the
series always converges and a non-summable series diverges to `-∞`. -/
theorem theorem_1_discriminatoryPricing_optimal {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) (S : Schedule) {d n : ℕ} {c δ : ℝ} (hd : 2 ≤ d) (hc : 0 < c) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hnd : n + 1 ≤ d) (hn : ∀ j, 1 ≤ j → IsIntroduced S j → IsUpgradeBoundAt S d j n) : (∀ j, 1 ≤ j → IsIntroduced S j → ∃ st, IsTerminalRun c S.s (sliceWeight S d δ j) j n st) ∧ ∀ runs : ℕ → Finset ℕ × (ℕ → ℝ), (∀ j, 1 ≤ j → IsIntroduced S j → IsTerminalRun c S.s (sliceWeight S d δ j) j n (runs j)) → Summable (discountedRevenue f S d c δ (discriminatoryPrices f ζ S.s c p n fun j => (runs j).2)) ∧ ∀ x' : ℕ → ℕ → ℝ, Summable (discountedRevenue f S d c δ x') → totalRevenue f S d c δ x' ≤ totalRevenue f S d c δ (discriminatoryPrices f ζ S.s c p n fun j => (runs j).2) := by sorry

end KashUpgrade
