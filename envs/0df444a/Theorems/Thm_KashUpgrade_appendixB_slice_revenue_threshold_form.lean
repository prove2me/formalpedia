-- Prove2me | Theorems.Thm_KashUpgrade_appendixB_slice_revenue_threshold_form
-- name    : KashUpgrade.appendixB_slice_revenue_threshold_form
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:58.252998+00:00
-- url     : https://prove2.me/theorems/aee0a0a2-6b43-4358-b015-50f5cbdff65b
-- title:
--   Appendix B, p.49 — the slice revenue in thresholds, with (37)–(38)
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$. Let $d\ge2$, $c>0$, $\delta\in(0,1)$, let $j\ge1$ be an introduction, and let $n$ bound the upgrade experience of slice $j$. Let $\theta$ be feasible for problem (12), and let $x$ be related to $\theta$ by (13). Then
--   $$
--   \mathrm{Revenue}_{[s_j,s_{j+1})}=A^j_js_j\theta^j_j\bigl(1-F(\theta^j_j)\bigr)+\sum_{i=1}^nA^j_{j+i}\bigl((s_{j+i}-s_{j+i-1})\theta^j_{j+i}-c\bigr)\bigl(1-F(\theta^j_{j+i})\bigr),
--   $$
--   with $A^j_j$ and $A^j_{j+i}$ as in (37) and (38).
--
--   This identity is the bridge from prices to thresholds: the weights count, discounted, the periods in which a customer of the slice pays each price increment.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (possibly infinite) sequence of introductions and prices x_{j,m} for m ≤ min(j−1, n), with x₀ = 0 → a schedule with J : ℕ∞ and a total function x : ℕ → ℕ → ℝ read through classPrice; reason: the same policies; unused entries of x enter nothing and class 0 always costs 0
--   - encoding: (10) sums over s_j ≤ t ≤ s_{j+1}+d−2 → a sum over all t with the printed age range, and s_{j+1} = ∞ at the last introduction of a finite schedule; reason: the age range is empty outside the printed times; a finite schedule has a last slice that the printed formula needs ∞ for
--   - encoding: (37)–(38) with s_{j+1} and s_{j+i} → t′ ≥ s_j when introduction j+1 does not exist, and A^j_{j+i} = 0 when introduction j+i does not exist; reason: the source writes them only for existing introductions; a customer never reaches a class that does not exist
--   - encoding: θ unconstrained except for the order in (12) → θ in the support [0, ζ]; reason: thresholds are types; a threshold above a finite ζ has 1−F = 0 and the term value of ζ
--   - generalization: n the maximum possible customer upgrade experience → any n bounding the upgrade experience of the slice; reason: the source’s n is such a bound, and the larger indices have zero weight or unused prices
--   - encoding: s_{j+i−i} in the two displays of p.49 → s_{j+i−1}; reason: a misprint: (12) and (13) have s_{j+i−1}
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Appendix B, p.49

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsUpgradeBoundAt
import Definitions.Def_KashUpgrade_sliceRevenue
import Definitions.Def_KashUpgrade_sliceWeight
import Definitions.Def_KashUpgrade_thresholdObjective
import Definitions.Def_KashUpgrade_ThresholdFeasible
import Definitions.Def_KashUpgrade_SatisfiesPriceRelations

namespace KashUpgrade

/-- **The slice revenue in thresholds.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Appendix B, p.49, with (37)–(38): for prices of the form
(13) built from a feasible threshold vector of (12), the slice revenue equals the objective of (12)
with the explicit coefficients `A^j_j` of (37) and `A^j_{j+i}` of (38).

**Formalization Note** The printed `s_{j+i-i}` on p.49 is read `s_{j+i-1}`, as in (12) and (13). -/
theorem appendixB_slice_revenue_threshold_form {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) (S : Schedule) {d : ℕ} {c δ : ℝ} (hd : 2 ≤ d) (hc : 0 < c) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) {j n : ℕ} (hj : 1 ≤ j) (hjS : IsIntroduced S j) (hn : IsUpgradeBoundAt S d j n) {θ : ℕ → ℝ} (hθ : ThresholdFeasible ζ p j n θ) {x : ℕ → ℕ → ℝ} (hx : SatisfiesPriceRelations S.s p c j n θ x) : sliceRevenue f S d c δ j x = thresholdObjective f c S.s (sliceWeight S d δ j) j n θ := by sorry

end KashUpgrade
