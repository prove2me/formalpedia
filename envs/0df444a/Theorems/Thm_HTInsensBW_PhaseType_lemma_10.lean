-- Prove2me | Theorems.Thm_HTInsensBW_PhaseType_lemma_10
-- name    : HTInsensBW.PhaseType.lemma_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:14:39.752992+00:00
-- url     : https://prove2.me/theorems/75b62470-0501-4128-ad64-237afdc1f104
-- title:
--   Lemma 10, p. 37 — tail and moment bounds from drift for continuous-time Markov chains
-- statement:
--   Let $(q_{ii'})$ be the transition rates of a continuous-time Markov chain on a countable state space $\mathcal X$: $q_{ii'}\ge0$ for $i'\neq i$, the chain is irreducible, and the total outgoing rate $\sum_{i'}q_{ii'}$ is bounded by a constant $\bar q$ (so the chain is nonexplosive). Let $\pi$ be a stationary distribution and $\overline X\sim\pi$. Let $V:\mathcal X\to\mathbb R_+$ have drift $\Delta V(i)=\sum_{i'\neq i}q_{ii'}(V(i')-V(i))$, and suppose:
--
--   1. there are $\gamma>0$ and $B>0$ with $\Delta V(i)\le-\gamma$ whenever $V(i)>B$;
--   2. $|V(i')-V(i)|\le\nu_{\max}$ whenever $q_{ii'}>0$;
--   3. $\sum_{i':V(i)<V(i')}q_{ii'}\le q_{\max}$ for every $i$.
--
--   Then for every nonnegative integer $j$
--   $$\mathbb P\big(V(\overline X)>B+2\nu_{\max}j\big)\le\Big(\frac{q_{\max}\nu_{\max}}{q_{\max}\nu_{\max}+\gamma}\Big)^{j+1},$$
--   and for every $m\in\mathbb Z_+$ the $m$-th moment is finite and
--   $$\mathbb E\big[V(\overline X)^m\big]\le(2B)^m+(4\nu_{\max})^m\Big(\frac{q_{\max}\nu_{\max}+\gamma}{\gamma}\Big)^mm!.$$
--
--   This is the continuous-time version of the Bertsimas–Gamarnik–Tsitsiklis bound; it turns the drift bounds of Lemmas 7 and 8 into tail and moment bounds.
--
--   **Formalization Note** Rates are encoded with zero diagonal, and condition (iii) of the paper ($\sup_i(-q_{ii})<\infty$) is the bound $\bar q$ on outgoing rates. "Positive recurrent and converging in distribution to $\overline X$" is encoded by taking $\pi$ a stationary probability distribution of the irreducible chain (with bounded rates the two are equivalent, and the limit law is $\pi$). $\nu_{\max}$ and $q_{\max}$ are upper bounds rather than the printed suprema; the bounds only weaken as they grow and the suprema are admissible values, so this is equivalent. Both are taken nonnegative.
-- source:
--   Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 37, Lemma 10 (Appendix A), (88)–(89)

import Mathlib
import Definitions.Def_HTInsensBW_PhaseType_Model

namespace HTInsensBW.PhaseType

/-- **Lemma 10, p. 37 — tail and moment bounds for continuous-time Markov chains.**
(Wang, Maguluri, Srikant, Ying, Heavy-traffic insensitive bounds for weighted proportionally fair bandwidth sharing policies, arXiv:1808.02120v2, p. 37, Lemma 10, (88)–(89).)
Let `q` be the transition rates of an irreducible continuous-time Markov chain on a countable
state space `X` with bounded total outgoing rates, and let `π` be a stationary distribution (the
law of the limit `X̄`). Let `V ≥ 0` satisfy: (i) `ΔV(i) ≤ -γ` whenever `V(i) > B` (`γ, B > 0`);
(ii) `|V(i') - V(i)| ≤ ν_max` whenever `q_{ii'} > 0`; and let `q_max` bound
`Σ_{i' : V(i) < V(i')} q_{ii'}` for every `i`. Then for every `j ∈ ℕ`
`P(V(X̄) > B + 2 ν_max j) ≤ (q_max ν_max / (q_max ν_max + γ))^{j+1}`, and for every `m ∈ ℕ`
`E[V(X̄)^m] ≤ (2B)^m + (4 ν_max)^m ((q_max ν_max + γ)/γ)^m m!` (finite).

**Formalization Note** Rates have zero diagonal (`q_ii = 0`); (iii) `sup_i (-q_ii) < ∞` is stated
as a bound `qbar` on the total outgoing rate `Σ_j q_ij`, which also makes the chain nonexplosive.
"Positive recurrent and converges in distribution to `X̄`" is encoded as: `π` is a stationary
probability distribution (for an irreducible nonexplosive chain this is equivalent to positive
recurrence, and `π` is the limit law). `ν_max` and `q_max` are upper bounds rather than the printed
suprema; both bounds weaken as they grow and the suprema are admissible, so this is equivalent.
They are taken `≥ 0` (a supremum of absolute values or of nonnegative sums). -/
theorem lemma_10 {X : Type*} [Countable X] (q : X → X → ℝ)
    (hq0 : ∀ i j, 0 ≤ q i j) (hqd : ∀ i, q i i = 0) (hqs : ∀ i, Summable (q i))
    (qbar : ℝ) (hqbar : ∀ i, ∑' j, q i j ≤ qbar)
    (hirr : ∀ i j, Relation.ReflTransGen (fun a b => 0 < q a b) i j)
    (π : X → ℝ) (hπ : IsStationary q π)
    (V : X → ℝ) (hV : ∀ i, 0 ≤ V i)
    (γ B : ℝ) (hγ : 0 < γ) (hB : 0 < B) (hdrift : ∀ i, B < V i → drift q V i ≤ -γ)
    (νmax : ℝ) (hν0 : 0 ≤ νmax) (hν : ∀ i j, 0 < q i j → |V j - V i| ≤ νmax)
    (qmax : ℝ) (hqm0 : 0 ≤ qmax)
    (hqmax : ∀ i, ∑' j, (if V i < V j then q i j else 0) ≤ qmax) :
    (∀ j : ℕ, ∑' i, (if B + 2 * νmax * j < V i then π i else 0) ≤
        (qmax * νmax / (qmax * νmax + γ)) ^ (j + 1)) ∧
    (∀ m : ℕ, Summable (fun i => π i * V i ^ m) ∧
      ∑' i, π i * V i ^ m ≤
        (2 * B) ^ m + (4 * νmax) ^ m * ((qmax * νmax + γ) / γ) ^ m * (m.factorial : ℝ)) := by sorry

end HTInsensBW.PhaseType
