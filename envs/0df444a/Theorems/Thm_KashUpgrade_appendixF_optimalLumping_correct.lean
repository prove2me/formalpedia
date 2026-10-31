-- Prove2me | Theorems.Thm_KashUpgrade_appendixF_optimalLumping_correct
-- name    : KashUpgrade.appendixF_optimalLumping_correct
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:23:02.50989+00:00
-- url     : https://prove2.me/theorems/77909312-13bf-419c-810c-9f39cceb8ed7
-- title:
--   Appendix F, pp.53–54 — correctness of OptimalLumping
-- statement:
--   Let the type law satisfy Assumption 2, with Myerson price $p^*$. Let $d\ge2$, $c>0$, $\delta\in(0,1)$, let $j\ge1$ be an introduction, and let $A$ be the weights (37)–(38). Then:
--
--   1. every state reached by OptimalLumping has a lumping that is a subset of the lumping of an optimal solution of (12);
--   2. OptimalLumping has a terminating run;
--   3. at every terminal state $(\mathcal L,\gamma)$ there is an optimal solution $\theta^*$ of (12) with $\theta^*_{j+i}=v^{-1}(\gamma_{j+i})$ at every index $1\le i\le n$ of positive weight; and if introduction $j+1$ exists, the vector with $\theta_j=p^*$ and $\theta_{j+i}=v^{-1}(\gamma_{j+i})$, $1\le i\le n$, is itself feasible and optimal for (12).
--
--   The maximizer chosen in each iteration is arbitrary, so 1. and 3. hold for every run.
--
--   Differences from the source:
--   - encoding: (1−F)/f monotonically decreasing on the support, differentiable density f → f > 0, (1−F)/f antitone and f differentiable on (0, ζ); reason: Lean has x/0 = 0, which on the closed interval would exclude Beta(2,2) with f(0) = 0; f > 0 on (0, ζ) follows from the source; the uniform example of p.24 is differentiable only on the interior
--   - encoding: (9) with the infimum over θ → infimum over (0, ζ), value in [0, ∞], real value taken; reason: v is defined on the support; the end points change nothing because of the minimum with ζ and the infimum; the value is finite under Assumption 2
--   - encoding: θ unconstrained except for the order in (12) → θ in the support [0, ζ]; reason: thresholds are types; a threshold above a finite ζ has 1−F = 0 and the term value of ζ
--   - encoding: (37)–(38) with s_{j+1} and s_{j+i} → t′ ≥ s_j when introduction j+1 does not exist, and A^j_{j+i} = 0 when introduction j+i does not exist; reason: the source writes them only for existing introductions; a customer never reaches a class that does not exist
--   - reading: k* ← argmax_{k∈S} γ_{j+k} → an arbitrary maximizer at every step, and existence of a terminating run; reason: the printed rule has ties, and for some choices the loop repeats a state forever; the example c = 6, intervals 1, 2, 3 is in the mission’s verification file
--   - encoding: the algorithm’s thresholds are feasible and optimal for (12) → when introduction j+1 exists, the vector (p*, v⁻¹(γ_{j+1}), …, v⁻¹(γ_{j+n})) is feasible and optimal, and in every case an optimal solution agrees with v⁻¹(γ) at the indices of positive weight; reason: for the last introduction of a finite schedule the classes j+i, i ≥ 1, do not exist and the printed algorithm reads undefined s_{j+i}
-- source:
--   Kash, Key & Zoumpoulis, Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services, SSRN 3934603 (Aug. 3, 2022), Appendix F, pp.53–54

import Mathlib
import Definitions.Def_KashUpgrade_Assumption2
import Definitions.Def_KashUpgrade_virtualInverse
import Definitions.Def_KashUpgrade_IsMyersonPrice
import Definitions.Def_KashUpgrade_IsOptimalThreshold
import Definitions.Def_KashUpgrade_IsTerminalRun
import Definitions.Def_KashUpgrade_lumpingOf
import Definitions.Def_KashUpgrade_sliceWeight

namespace KashUpgrade

/-- **Correctness of OptimalLumping.** Kash, Key & Zoumpoulis, *Optimal Pricing and Introduction Timing of Technology Upgrades in Subscription-Based Services*, SSRN 3934603 (Aug. 3, 2022), Appendix F, pp.53–54, for the weights (37)–(38) of a slice
`j ≥ 1`:

1. the lumping of every state reached from `(∅, γ⁰)` is contained in the lumping of an optimal
   solution of (12);
2. a terminating run exists;
3. at a terminal state, `v⁻¹(γ_i)` is an optimal solution of (12): there is an optimal solution equal
   to it at every index of positive weight, and if introduction `j + 1` exists, the vector with
   `θ_j = p*` and `θ_i = v⁻¹(γ_i)` for `i ≠ j` is itself feasible and optimal for (12).

**Formalization Note** The choice of `k*` is free at every step, so 1. and 3. hold for every run. An
index of zero weight does not enter the objective of (12), and on a block of zero weight (20) reads
`0 / 0`, which the paper leaves undefined; the first half of 3. says nothing about such indices.
For the last introduction of a finite schedule the indices `j + i`, `i ≥ 1`, do not exist and the
printed algorithm reads undefined `s_{j+i}`, so the second half of 3. is stated when introduction
`j + 1` exists. -/
theorem appendixF_optimalLumping_correct {f : ℝ → ℝ} {ζ : ENNReal} (hf : Assumption2 f ζ) {p : ℝ} (hp : IsMyersonPrice f p) (S : Schedule) {d : ℕ} {c δ : ℝ} (hd : 2 ≤ d) (hc : 0 < c) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) {j : ℕ} (n : ℕ) (hj : 1 ≤ j) (hjS : IsIntroduced S j) : (∀ st, Relation.ReflTransGen (OLStep c S.s (sliceWeight S d δ j) j n) (∅, initialGamma c S.s) st → ∃ θ, IsOptimalThreshold f ζ p c S.s (sliceWeight S d δ j) j n θ ∧ st.1 ⊆ lumpingOf j n θ) ∧ (∃ st, IsTerminalRun c S.s (sliceWeight S d δ j) j n st) ∧ ∀ st, IsTerminalRun c S.s (sliceWeight S d δ j) j n st → (∃ θ, IsOptimalThreshold f ζ p c S.s (sliceWeight S d δ j) j n θ ∧ ∀ i, 1 ≤ i → i ≤ n → 0 < sliceWeight S d δ j (j + i) → θ (j + i) = (virtualInverse f ζ (st.2 (j + i))).toReal) ∧ (IsIntroduced S (j + 1) → IsOptimalThreshold f ζ p c S.s (sliceWeight S d δ j) j n (fun i => if i = j then p else (virtualInverse f ζ (st.2 i)).toReal)) := by sorry

end KashUpgrade
