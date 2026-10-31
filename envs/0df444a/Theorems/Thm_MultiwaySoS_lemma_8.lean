-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_8
-- name    : MultiwaySoS.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:19:42.634544+00:00
-- url     : https://prove2.me/theorems/77af78b7-bb7a-4858-851a-707100d575bb
-- title:
--   Lemma 8 — the Lyapunov function $\Psi^t=\sqrt{\Phi(\mathscr Q^t)+\Xi^t}$: bounded increments $K_1(\tau)$ and drift $-\delta/(8\sqrt2n^2)$ above $K_2(\tau,\delta)$
-- statement:
--   Under the hypotheses of Theorem 2, run Algorithm 2 with an arg-min commit rule and write $\Phi^t=\Phi(\mathscr Q^t)$, $B=2n^2$,
--   $$K_1(\tau)=6\tau^2+9\tau+2\tau\log(3+4\tau)+8,\qquad K_2(\tau,\delta)=\sqrt{2\max\{c_1(\tau,\delta),c_2(\tau)\}},$$
--   $$c_1(\tau,\delta)=\frac{4B^2(8\tau^2+2\tau\log(3+4\tau)+20\tau+1)^2}{\delta^2}\ \ (27),\qquad c_2(\tau)=32\tau^2+4\tau(8\tau+2\ln(1+4\tau))\ \ (28).$$
--   There is a process $\Xi^t$ adapted to $\{\mathcal F^t\}$ with, almost surely,
--   $$0\le\Xi^t\le2\tau\Big(\sqrt{8\Phi^t}+8\tau+2\ln(1+4\tau)\Big)\qquad(t\le T),$$
--   such that $\Psi^t=\sqrt{\Phi^t+\Xi^t}$ satisfies, for $\tau\le t<T$:
--
--   1. **bounded variation**: $|\Psi^{t+1}-\Psi^t|\le K_1(\tau)$ almost surely;
--   2. **expected decrease**: $\mathbb E[\Psi^{t+1}-\Psi^t\mid\mathcal F^t]\le-\dfrac{\delta}{8\sqrt2n^2}$ almost surely on $\{\Psi^t\ge K_2(\tau,\delta)\}$.
--
--   These are the hypotheses of Lemma 3 for $\Upsilon^t=\Psi^t$; they are the main technical step of the paper.
--
--   Differences from the source:
--   - generalization: drift conditions "for $t\ge\tau+1$" → for $\tau\le t<T$; reason: the proof\'s index runs from $\tau+1$ (p.43) and Lemma 3 is applied from $\tau$ (p.24); the range contains the printed one
--   - reading: "a non-negative stochastic process $\Xi^t$" → a process adapted to $\{\mathcal F^t\}$; reason: Lemma 3 requires an adapted process; without it $\Xi$ could look ahead and the lemma would be empty
--   - reading: $\mathbb E[\Psi^{t+1}-\Psi^t\mid\Psi^t\ge K_2]$ → conditional on $\mathcal F^t$, on the event $\{\Psi^t\ge K_2\}$; reason: this is the form Lemma 3(b) consumes
--   - encoding: a conditional expectation given $\mathcal F^t$ on the event $\{\cdot\ge K_2\}$ → its defining form: $\int_A(\cdot)\,dP\le c\,P(A)$ for every $A\in\mathcal F^t$ contained in the event; reason: equivalent for integrable increments; avoids the junk value of an undefined conditional expectation
--   - reading: the bounds on $\Xi^t$ and condition (a), stated without qualifier → almost surely; reason: Assumption 1 and Assumption 2 hold only almost surely, so the construction can fail on a null set
--   - encoding: "$K_2(\tau,\delta)=\dots=O(n^2\tau^2/\delta)$" → $K_2$ given by its explicit formula; the $O(\cdot)$ is not stated; reason: the $O(\cdot)$ is a comment on the size of the explicit constant
--   - reading: "the distribution $\lambda^t$ from which the type $I^t$ is sampled is itself a random quantity, which is $\mathcal F^{t-1}$-measurable. Conditioned on the sequence $\{\lambda^t\}$, $\{I^t\}$ are assumed to be mutually independent" (p.15) → $P(I^t=i\mid\mathcal F^{t-1})=\lambda^t_i$, written as $P(A\cap\{I^t=i\})=\int_A\lambda^t_i\,dP$ for $A\in\mathcal F^{t-1}$; reason: this is the sampling sentence of the page; the conditional-independence sentence is not assumed separately, because it would add no constraint the proof uses once each $I^t$ is drawn from the predictable $\lambda^t$
--   - reading: Assumption 1: "almost surely $\bar\lambda$ satisfies GPG$_{\epsilon_0}$"; "we fix an optimal basic feasible solution $x^*$ and its basis $\mathcal M_+$" (p.16) → $\bar\lambda$ and $x^*$ are random, the basis $\mathcal M_+$ is one fixed set, GPG holds almost surely; Assumption 2 and the offline requirement hold almost surely; reason: Algorithm 2 needs a fixed $\mathcal M_+$; a deterministic $\bar\lambda$ is the constant case, so this reading is the stronger statement
--   - generalization: $0<\delta<\epsilon_0$ (Assumption 2, Theorem 2) → $0<\delta\le\epsilon_0$; reason: p.17 (example 2) and p.18 use $\delta=\epsilon_0$; the range contains the printed one
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - reading: second line of (10): $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{im}$ → $Q_{i^\prime m}+\mathbb 1\{i^\prime=i\}<M_{i^\prime m}$; reason: obvious intent; both entries equal $1$ for $i,i^\prime\in\mathcal I(m)$
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - encoding: $\sum_{s=1}^{t-2\tau}\hat\lambda^s$ in Assumption 2 → `Finset.Icc 1 (t - 2 * τ)` with truncated subtraction; reason: the sum is empty for $t\le2\tau$, the paper's meaning; no instance changes
--   - generalization: the bounds on $\Xi^t$ "for all $t\in[T]$" → the same bounds for $0\le t\le T$; reason: (22) at $t=0$ gives $\Xi^0=2\tau$, which satisfies them; the range contains the printed one
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 8, pp.23–24; constants (27), (28), p.44

import Mathlib
import Definitions.Def_MultiwaySoS_Setting

open MeasureTheory

namespace MultiwaySoS

/-- Lemma 8 (arXiv:2112.04622v3, pp.23–24, constants (27), (28) on p.44).

Under the hypotheses of Theorem 2 and for Algorithm 2 with an arg-min commit rule, write
`Φ^t = Φ(𝒬^t)`, `Bc = 2n²`,
`K₁(τ) = 6τ² + 9τ + 2τ log(3 + 4τ) + 8`,
`c₁(τ, δ) = 4Bc²(8τ² + 2τ log(3 + 4τ) + 20τ + 1)²/δ²` (27),
`c₂(τ) = 32τ² + 4τ(8τ + 2 ln(1 + 4τ))` (28),
`K₂(τ, δ) = √(2 max{c₁(τ, δ), c₂(τ)})`.
There is an `{F^t}`-adapted process `Ξ^t` with, almost surely, `0 ≤ Ξ^t ≤ 2τ(√(8Φ^t) + 8τ + 2 ln(1 + 4τ))`
for `t ≤ T`, such that `Ψ^t = √(Φ^t + Ξ^t)` satisfies, for `τ ≤ t < T`:
(a) `|Ψ^{t+1} − Ψ^t| ≤ K₁(τ)` almost surely;
(b) `E[Ψ^{t+1} − Ψ^t | F^t] ≤ −δ/(8√2 n²)` almost surely on `{Ψ^t ≥ K₂(τ, δ)}`.

**Formalization Note.** (b) is written in the defining form of the conditional expectation:
`∫_A (Ψ^{t+1} − Ψ^t) dP ≤ −δ/(8√2n²) · P(A)` for every `A ∈ F^t` contained in `{Ψ^t ≥ K₂}`. The
`O(n²τ²/δ)` comment on `K₂` is not part of the statement. -/
theorem lemma_8 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (T τ : ℕ) (ε₀ δ : ℝ) (Arr : ℕ → Ω → Fin n)
    (lam : ℕ → Ω → Fin n → ℝ) (lamBar : Ω → Fin n → ℝ) (xStar : Ω → Fin d → ℝ)
    (lamHat : ℕ → Ω → Fin n → ℝ) (c : Fin n → ℝ)
    (hS : IsSetting I B P T τ ε₀ δ Arr lam lamBar xStar lamHat c)
    (pick : ℕ → State n d → Fin n → Fin d) (hpick : IsArgminRule I B σ pick) :
    let F := arrivalFiltration Arr
    let Φt : ℕ → Ω → ℝ := fun t ω =>
      ((Phi B σ (fun i m => (run I (fun i => c i * T) pick (fun s => Arr s ω) t).Qv I i m) : ℤ) : ℝ)
    let Bc : ℝ := 2 * (n : ℝ) ^ 2
    let K₁ : ℝ := 6 * (τ : ℝ) ^ 2 + 9 * τ + 2 * τ * Real.log (3 + 4 * τ) + 8
    let c₁ : ℝ := 4 * Bc ^ 2 * (8 * (τ : ℝ) ^ 2 + 2 * τ * Real.log (3 + 4 * τ) + 20 * τ + 1) ^ 2 / δ ^ 2
    let c₂ : ℝ := 32 * (τ : ℝ) ^ 2 + 4 * τ * (8 * τ + 2 * Real.log (1 + 4 * τ))
    let K₂ : ℝ := Real.sqrt (2 * max c₁ c₂)
    ∃ Ξ : ℕ → Ω → ℝ, (∀ t, Measurable[F t] (Ξ t)) ∧
      (∀ t, t ≤ T → ∀ᵐ ω ∂P, 0 ≤ Ξ t ω ∧
        Ξ t ω ≤ 2 * τ * (Real.sqrt (8 * Φt t ω) + 8 * τ + 2 * Real.log (1 + 4 * τ))) ∧
      (∀ t, τ ≤ t → t < T → ∀ᵐ ω ∂P,
        |Real.sqrt (Φt (t + 1) ω + Ξ (t + 1) ω) - Real.sqrt (Φt t ω + Ξ t ω)| ≤ K₁) ∧
      (∀ t, τ ≤ t → t < T → ∀ A : Set Ω, MeasurableSet[F t] A →
        A ⊆ {ω | K₂ ≤ Real.sqrt (Φt t ω + Ξ t ω)} →
        ∫ ω in A, (Real.sqrt (Φt (t + 1) ω + Ξ (t + 1) ω) - Real.sqrt (Φt t ω + Ξ t ω)) ∂P ≤
          -(δ / (8 * Real.sqrt 2 * (n : ℝ) ^ 2)) * (P A).toReal) := by sorry

end MultiwaySoS
