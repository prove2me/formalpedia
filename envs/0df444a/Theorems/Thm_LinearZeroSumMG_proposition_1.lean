-- Prove2me | Theorems.Thm_LinearZeroSumMG_proposition_1
-- name    : LinearZeroSumMG.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:51.849047+00:00
-- url     : https://prove2.me/theorems/d7991c78-fa4b-4883-b6f8-c7ccf0b01c74
-- title:
--   Proposition 1, p.7 — weak duality
-- statement:
--   **Proposition 1 (Weak duality).** Let $(\pi^*,\nu^*)$ be a pair of (measurable, stochastic, Markov) policies that is a Nash equilibrium at every step: $V^{\pi^*,\nu^*}_h(x)=V^{*,\nu^*}_h(x)=V^{\pi^*,*}_h(x)$ for all $h\in[H]$ and $x\in\mathcal S$, and write $V^*_h=V^{\pi^*,\nu^*}_h$, $Q^*_h=Q^{\pi^*,\nu^*}_h$. Then for every policy pair $(\pi,\nu)$, every $h\in[H]$ and every $(x,a,b)$,
--   $$
--   Q^{\pi,*}_h(x,a,b)\le Q^*_h(x,a,b)\le Q^{*,\nu}_h(x,a,b),\qquad V^{\pi,*}_h(x)\le V^*_h(x)\le V^{*,\nu}_h(x),
--   $$
--   $$
--   Q^{\pi,*}_h(x,a,b)\le Q^{\pi,\nu}_h(x,a,b)\le Q^{*,\nu}_h(x,a,b),\qquad V^{\pi,*}_h(x)\le V^{\pi,\nu}_h(x)\le V^{*,\nu}_h(x).
--   $$
--
--   The Nash value is sandwiched between the two best-response values, which is why the duality gap $V^{*,\nu}_1-V^{\pi,*}_1$ measures distance from equilibrium.
--
--   Differences from the source:
--   - reading: a Nash equilibrium (π*, ν*) defined by (2) at step 1, V^{π*,ν*}_1(x₁) = V^{*,ν*}_1(x₁) = V^{π*,*}_1(x₁) for x₁ ∈ 𝒮, under unspecified regularity conditions → (π*, ν*) is a Nash equilibrium at every step h ∈ [H] and state, as a hypothesis; reason: V*_h and Q*_h are "the values of the NE at step h" (p.6); with an equilibrium at step 1 only, Q^{π,*}_h ≤ Q*_h can fail at states not reachable at step 1
--   - encoding: feature map, policies, CCE rule and rounding with no measurability stated; finite action set → φ jointly measurable, policies measurable in the state, CCE rule and rounding rule Borel measurable, A with its discrete σ-algebra; reason: without measurability the expectations ℙ_h V and the conditional laws of the analysis are undefined; these conditions exclude only such cases
--   - encoding: V^{π,ν}_h, Q^{π,ν}_h as expected sums of rewards along a trajectory; V^{*,ν} = max_π, V^{π,*} = min_ν (p.6) → backward Bellman recursion for a fixed pair; best responses as ⨆/⨅ over measurable stochastic Markov policies; reason: for a fixed Markov policy pair the trajectory expectation equals the recursion; same instances
--   - encoding: a finite action set → a finite nonempty action set; reason: with no action there are no policies and the extrema are undefined; nondegeneracy only
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Proposition 1, p.7; (2), p.6

import Mathlib
import Definitions.Def_LinearZeroSumMG_bestV1

namespace LinearZeroSumMG

/-- **Proposition 1 (Weak Duality).**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Proposition 1, p.7: "For each policy
pair `(π, ν)` and each `h ∈ [H]`, `(x, a, b) ∈ 𝒮 × 𝒜 × 𝒜`, we have
`Q^{π,*}_h(x, a, b) ≤ Q^*_h(x, a, b) ≤ Q^{*,ν}_h(x, a, b)`, `V^{π,*}_h(x) ≤ V^*_h(x) ≤ V^{*,ν}_h(x)`,
`Q^{π,*}_h(x, a, b) ≤ Q^{π,ν}_h(x, a, b) ≤ Q^{*,ν}_h(x, a, b)`, `V^{π,*}_h(x) ≤ V^{π,ν}_h(x) ≤ V^{*,ν}_h(x)`."
Here (p.6) `V^*_h(x) := V^{π^*,ν^*}_h(x)` and `Q^*_h(x, a, b) := Q^{π^*,ν^*}_h(x, a, b)` are the values of a
Nash equilibrium `(π^*, ν^*)`.

The NE hypothesis: `π^*`, `ν^*` are policies that are best responses to each other at every step:
`V^{π^*,ν^*}_h(x) = V^{*,ν^*}_h(x) = V^{π^*,*}_h(x)` for all `h ∈ [1, H]`, `x ∈ S`.

**Formalization Note** The paper defines an NE by (2), at step 1 for every initial state, and assumes
"appropriate regularity conditions so that an NE exists and their value is unique" (p.6). The
proposition is stated with an NE at every step, which is what `V^*_h`, "the values of the NE at
step `h`", requires; with step 1 only, `Q^{π,*}_h ≤ Q^*_h` can fail at states not reachable at step 1. A
finite nonempty action set makes all policy classes nonempty. -/
theorem proposition_1 {S A : Type*} [MeasurableSpace S] [MeasurableSpace A] [Fintype A]
    [Nonempty A] (G : MarkovGame S A) (πs νs : ℕ → S → A → ℝ) (hπs : IsPolicy πs)
    (hνs : IsPolicy νs)
    (hNE : ∀ h ∈ Finset.Icc 1 G.H, ∀ x,
      Vval G πs νs h x = bestV1 G νs h x ∧ Vval G πs νs h x = bestV2 G πs h x)
    (π ν : ℕ → S → A → ℝ) (hπ : IsPolicy π) (hν : IsPolicy ν) (h : ℕ)
    (hh : h ∈ Finset.Icc 1 G.H) (x : S) (a b : A) :
    (bestQ2 G π h x a b ≤ Qval G πs νs h x a b ∧ Qval G πs νs h x a b ≤ bestQ1 G ν h x a b) ∧
    (bestV2 G π h x ≤ Vval G πs νs h x ∧ Vval G πs νs h x ≤ bestV1 G ν h x) ∧
    (bestQ2 G π h x a b ≤ Qval G π ν h x a b ∧ Qval G π ν h x a b ≤ bestQ1 G ν h x a b) ∧
    (bestV2 G π h x ≤ Vval G π ν h x ∧ Vval G π ν h x ≤ bestV1 G ν h x) := by sorry

end LinearZeroSumMG
