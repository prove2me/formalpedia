-- Prove2me | Theorems.Thm_NegativeDP_Stationary_lemma41a
-- name    : NegativeDP.Stationary.lemma41a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:23.55912+00:00
-- url     : https://prove2.me/theorems/5c427396-866b-4271-9215-acaa9e73eb05
-- title:
--   Lemma 4.1 (a) — the semi-Markov π* built from the conditional laws of aₙ given (s₁, sₙ) has the same laws of (s₁, sₙ, aₙ, sₙ₊₁)
-- statement:
--   In the negative dynamic programming problem, let $\pi$ be any policy. For each stage $n$ let $\kappa'_n(\cdot\mid s_1,s_n)$ be a probability kernel from $S\times S$ to $A$ which is a version of the conditional distribution of the action $a_n$ given the initial state $s_1$ and the current state $s_n$ under $e_\pi$: for every initial state $s_1$ and every Borel $B\subseteq S\times A$,
--
--   $$e_\pi\big[\pi_n(\{a:(s_n,a)\in B\}\mid h_n)\big]=e_\pi\big[\kappa'_n(\{a:(s_n,a)\in B\}\mid s_1,s_n)\big],$$
--
--   i.e. the joint law of $(s_n,a_n)$ under $\pi$ from $s_1$ is the law of $s_n$ followed by $\kappa'_n(\cdot\mid s_1,\cdot)$. Let $\pi^*$ be the random semi-Markov policy whose $n$th action is drawn from $\kappa'_n(\cdot\mid s_1,s_n)$. Then for every $n$, every initial state $s_1$ and every $r\in M(SSAS)$,
--
--   $$e_\pi r(s_1,s_n,a_n,s_{n+1})=e_{\pi^*}r(s_1,s_n,a_n,s_{n+1}).$$
--
--   This is the key step in the proof of Theorem 4.1: the conditional laws of the actions given $(s_1,s_n)$ already determine all expected returns, so the random semi-Markov policy $\pi^*$ earns the same expected return as $\pi$ for every return function.
--
--   The paper states the lemma for the discounted, positive and negative cases (with each case's class $M$) and introduces $\pi^*$ inside the proof of Theorem 4.1; this item takes $\pi^*$'s defining property as a hypothesis and uses the negative-case class $M$ (non-positive extended-real Borel test functions).
--
--   **Formalization Note.** Lean stages are numbered from $0$, so stage $n$ here is the paper's stage $n+1$. The conditional-distribution property is stated for every initial state and every Borel set $B$, as an identity of integrals against the law of the history before the action. Expectations of a test function $u\le 0$ are computed as $-\int(-u)$ in $[0,\infty]$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 876, Lemma 4.1 (a) (π* defined in the proof of Theorem 4.1, p. 876)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Lemma 4.1 (a) (p. 876), negative-case `M`. Let `κ'ₙ(s₁, sₙ, ·)` be a version of the
conditional distribution of `aₙ` given `(s₁, sₙ)` under `e_π`: for every initial state `s₁` the
joint law of `(sₙ, aₙ)` under `π` is the law of `sₙ` followed by `κ'ₙ(s₁, ·)`. Let `π*` be the
random semi-Markov plan built from the `κ'ₙ`. Then for every stage and every `u ∈ M(SSAS)`,
`e_π u(s₁, sₙ, aₙ, sₙ₊₁) = e_{π*} u(s₁, sₙ, aₙ, sₙ₊₁)`. -/
theorem lemma41a (P : Problem S A) (π : Plan (S := S) (A := A))
    (κ' : ℕ → Kernel (S × S) A) (hκ' : ∀ n, IsMarkovKernel (κ' n))
    (hcond : ∀ (n : ℕ) (s : S) (B : Set (S × A)), MeasurableSet B →
      ∫⁻ h, π.κ n h {a | (h.2, a) ∈ B} ∂historyLaw P π s n =
        ∫⁻ h, κ' n (s, h.2) {a | (h.2, a) ∈ B} ∂historyLaw P π s n) :
    ∀ (n : ℕ) (s : S) (u : S × (S × A × S) → EReal), IsNegM u →
      stageExp P π s n (fun y => u (s, y)) =
        stageExp P (semiMarkovPlan κ' hκ') s n (fun y => u (s, y)) := by sorry

end NegativeDP.Stationary
