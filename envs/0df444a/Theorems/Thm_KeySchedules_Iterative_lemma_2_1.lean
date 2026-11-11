-- Prove2me | Theorems.Thm_KeySchedules_Iterative_lemma_2_1
-- name    : KeySchedules.Iterative.lemma_2_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T22:51:24.083085+00:00
-- url     : https://prove2.me/theorems/8fbb2226-b1ab-442d-af5f-35fe72210b78
-- title:
--   Lemma 2.1 — the expectation method: Adv ≤ Δ = E[g★(Θ_0)] ≤ E[g(Θ_0)] + Pr[Θ_0 ∈ 𝒯_bad]
-- statement:
--   Let $S_0$ (ideal) and $S_1$ (real) be systems, and let the transcripts carry auxiliary information $a$ from a finite set, revealed after the query phase, with transcript probabilities $p_b(\bar\tau,a)\ge0$ such that $\sum_a p_b(\bar\tau,a)$ is the transcript probability of $S_b$. A transcript is attainable when $p_0>0$, and $\mathcal T$ is the set of attainable transcripts allowed by the game. Suppose $\mathcal T_{\mathrm{bad}}\subseteq\mathcal T$ and $g:\mathcal T\to\mathbb R_{\ge0}$ satisfy
--   $$\frac{p_1(\tau)}{p_0(\tau)}\ge1-g(\tau)\qquad(\tau\in\mathcal T\setminus\mathcal T_{\mathrm{bad}}),$$
--   and let $g^\star=1$ on $\mathcal T_{\mathrm{bad}}$ and $\min\{1,g\}$ elsewhere. Then for every adversary $\mathcal A$,
--   $$\mathrm{Adv}_{\mathcal E}(\mathcal A)\le\Delta_{\mathcal E}(\mathcal A):=\mathbb E[g^\star(\Theta_0)]\le\mathbb E[g(\Theta_0)]+\Pr[\Theta_0\in\mathcal T_{\mathrm{bad}}].$$
--   This is the paper's formulation of Hoang and Tessaro's expectation method, the security framework to which the key-schedule results apply.
--
--   Differences from the source:
--
--   - generalization: 𝒯, the attainable transcripts allowed by the game → an arbitrary set `allowed` of query-response transcripts (the hypotheses on its attainable elements), for adversaries whose complete transcripts are allowed; reason: allowed = all transcripts is the printed lemma; allowed = the transcripts within q queries is how Theorem 3.1 uses it
--   - generalization: auxiliary information of the system, revealed after the query phase → any nonnegative p_b(τ̄, a) over a finite set of values a whose sum over a is the system's p_b(τ̄); reason: the paper's auxiliary transcript probabilities have these properties; the Lean statement assumes nothing more
--   - generalization: 𝒯_bad ⊆ 𝒯 → any set 𝒯_bad of (τ̄, a); reason: elements outside 𝒯 are never attained and carry weight 0; the subset case is included
--   - reading: every adversary → every finite mixture of deterministic strategies that, for some q, never asks more than q queries to any oracle; reason: an adversary is an algorithm that produces an output; with finite alphabets a strategy that stops on every response sequence has a query bound (König's lemma); with finitely many behaviours, finite mixtures of such strategies cover randomized adversaries
--   - encoding: Adv_ℰ(A) for the game of ℰ, E[·] and Pr[·] over Θ_0 → advantage of S0, S1 (the adversary's output depends on the query-response transcript only), sums over complete transcripts weighted by p_0(τ̄, a); reason: Pr[Θ_b = τ] = p_b(τ) for complete transcripts, as on p. 8
--   - encoding: p_1(τ)/p_0(τ) ≥ 1 − g(τ) for τ ∈ 𝒯 ∖ 𝒯_bad → (1 − g(τ)) · p_0(τ) ≤ p_1(τ) for attainable τ (p_0(τ) > 0) outside the bad set; reason: multiplying by p_0(τ) > 0; same condition, no division
--   - encoding: a system: a finite tuple of possibly randomized, possibly stateful oracles with joint randomness → a System: its transcript probabilities p(τ) (p ≥ 0, p([]) = 1, ∑_y p(τ ++ [(x, y)]) = p(τ)); reason: these are exactly the paper's p_b(τ), which determine every adversary's view; every system has them and every such function is a system
--   - reading: a finite tuple of oracles whose query and response sets the paper leaves implicit → a finite oracle set ι, finite query and response alphabets Q, R, each query addressed to the oracle oracleOf x; reason: the paper calls 𝒯_q 'the finite set', which needs finite alphabets; oracle-specific alphabets embed in common ones, a system giving probability 0 to responses an oracle cannot return
--   - encoding: a non-negative function g : 𝒯 → ℝ → g defined on all pairs, its non-negativity required only on attainable pairs in the hypothesis's transcript set; reason: g★ is only ever weighted by p_0 > 0 on those pairs, so values elsewhere are never used; the paper's g extends to such a function
-- source:
--   Beierle, Choi, Hhan, Jha, Kim, Minimizing Key Schedules for Key-Alternating Ciphers, STOC 2027 submission (manuscript sha256 cd9f815b…), p. 8, Lemma 2.1

import Mathlib
import Definitions.Def_KeySchedules_Iterative_Oracles

namespace KeySchedules.Iterative

/-- Lemma 2.1 (expectation method, p. 8). Two systems `S0` (ideal) and `S1` (real) are given
together with transcript probabilities `P_b(τ̄, a)` that append auxiliary information
`a ∈ Aux` to the query-response transcript `τ̄` (nonnegative, with `∑_a P_b(τ̄, a) = p_b(τ̄)`).
The game allows the query-response transcripts in `allowed`; a transcript `(τ̄, a)` is
attainable when `P_0(τ̄, a) > 0`, and `𝒯` is the set of attainable allowed transcripts.
Suppose `𝒯_bad` and `g ≥ 0` on `𝒯` satisfy `P_1(τ) ≥ (1 − g(τ)) P_0(τ)` for every
`τ ∈ 𝒯 ∖ 𝒯_bad`. Then every adversary (a mixture of strategies that stop after at most `q`
queries per oracle, for some `q`, and whose complete transcripts are allowed) has
`Adv(A) ≤ Δ(A) = E[g★(Θ_0)] ≤ E[g(Θ_0)] + Pr[Θ_0 ∈ 𝒯_bad]`. -/
theorem lemma_2_1 {I : Interface} {Aux : Type} [Fintype Aux] (S0 S1 : System I)
    (P0 P1 : Transcript I → Aux → ℝ) (hP0 : ∀ τ a, 0 ≤ P0 τ a) (hP1 : ∀ τ a, 0 ≤ P1 τ a)
    (hS0 : ∀ τ, ∑ a, P0 τ a = S0.prob τ) (hS1 : ∀ τ, ∑ a, P1 τ a = S1.prob τ)
    (allowed : Set (Transcript I)) (bad : Set (Transcript I × Aux))
    (g : Transcript I × Aux → ℝ)
    (hg : ∀ τ ∈ allowed, ∀ a, 0 < P0 τ a → 0 ≤ g (τ, a))
    (hratio : ∀ τ ∈ allowed, ∀ a, 0 < P0 τ a → (τ, a) ∉ bad →
      (1 - g (τ, a)) * P0 τ a ≤ P1 τ a)
    (q : ℕ) (A : Adversary I) (hA : A.WithinBudget q)
    (hAllowed : ∀ i τ, (A.strat i).Complete τ → τ ∈ allowed) :
    advantage S0.prob S1.prob A
        ≤ A.sumComplete (fun τ => ∑ a, P0 τ a * gStar bad g (τ, a)) ∧
    A.sumComplete (fun τ => ∑ a, P0 τ a * gStar bad g (τ, a))
        ≤ A.sumComplete (fun τ => ∑ a, P0 τ a * g (τ, a))
          + A.sumComplete (fun τ => ∑ a, bad.indicator (fun x => P0 x.1 x.2) (τ, a)) := by sorry

end KeySchedules.Iterative
