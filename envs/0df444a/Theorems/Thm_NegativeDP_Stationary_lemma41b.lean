-- Prove2me | Theorems.Thm_NegativeDP_Stationary_lemma41b
-- name    : NegativeDP.Stationary.lemma41b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:54:22.815595+00:00
-- url     : https://prove2.me/theorems/c9f1677b-1aff-49e3-b2ef-9a079daff714
-- title:
--   Lemma 4.1 (b) — the random Markov π** built from the conditional laws of aₙ given sₙ under pe_π has the same p-averaged laws
-- statement:
--   In the negative dynamic programming problem, let $\pi$ be any policy and $p$ a probability measure on $S$ (the law of the initial state). For each stage $n$ let $\kappa''_n(\cdot\mid s_n)$ be a probability kernel from $S$ to $A$ which is a version of the conditional distribution of $a_n$ given $s_n$ under $pe_\pi$: for every Borel $B\subseteq S\times A$,
--
--   $$pe_\pi\big[\pi_n(\{a:(s_n,a)\in B\}\mid h_n)\big]=pe_\pi\big[\kappa''_n(\{a:(s_n,a)\in B\}\mid s_n)\big].$$
--
--   Let $\pi^{**}$ be the random Markov policy whose $n$th action is drawn from $\kappa''_n(\cdot\mid s_n)$. Then for every $n$ and every $r\in M(SAS)$,
--
--   $$pe_\pi r(s_n,a_n,s_{n+1})=pe_{\pi^{**}}r(s_n,a_n,s_{n+1}).$$
--
--   This is the averaged counterpart of Lemma 4.1 (a): when the initial state is drawn from $p$, a random Markov policy reproduces all $p$-averaged expected returns of $\pi$.
--
--   The paper states the lemma for the discounted, positive and negative cases and introduces $\pi^{**}$ inside the proof of Theorem 4.1; this item takes $\pi^{**}$'s defining property as a hypothesis and uses the negative-case class $M$.
--
--   **Formalization Note.** Lean stages are numbered from $0$. $pe_\pi u$ is $\int e_\pi u\,dp$, computed as $-\int\!\!\int(-u)$ in $[0,\infty]$.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 876, Lemma 4.1 (b) (π** defined in the proof of Theorem 4.1, p. 876)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_NegativeDP_Stationary_Model
open MeasureTheory ProbabilityTheory Filter Topology
open DiscountedDP.Stationary (Hist Plan MarkovPlan MarkovPlan.toPlan stationary)

namespace NegativeDP.Stationary

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Lemma 4.1 (b) (p. 876), negative-case `M`. Let `p ∈ P(S)`, let `κ''ₙ(sₙ, ·)` be a
version of the conditional distribution of `aₙ` given `sₙ` under `pe_π`, and let `π**` be the
random Markov plan built from the `κ''ₙ`. Then for every stage and every `u ∈ M(SAS)`,
`pe_π u(sₙ, aₙ, sₙ₊₁) = pe_{π**} u(sₙ, aₙ, sₙ₊₁)`. -/
theorem lemma41b (P : Problem S A) (π : Plan (S := S) (A := A))
    (p : Measure S) [IsProbabilityMeasure p]
    (κ'' : ℕ → Kernel S A) (hκ'' : ∀ n, IsMarkovKernel (κ'' n))
    (hcond : ∀ (n : ℕ) (B : Set (S × A)), MeasurableSet B →
      ∫⁻ s, ∫⁻ h, π.κ n h {a | (h.2, a) ∈ B} ∂historyLaw P π s n ∂p =
        ∫⁻ s, ∫⁻ h, κ'' n h.2 {a | (h.2, a) ∈ B} ∂historyLaw P π s n ∂p) :
    ∀ (n : ℕ) (u : S × A × S → EReal), IsNegM u →
      pInt p (fun s => stageExp P π s n u) =
        pInt p (fun s => stageExp P (randomMarkovPlan κ'' hκ'') s n u) := by sorry

end NegativeDP.Stationary
