-- Prove2me | Theorems.Thm_IntervalExplore_KT1_Supplement_lemma_9
-- name    : IntervalExplore.KT1.Supplement.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:01:49.582191+00:00
-- url     : https://prove2.me/theorems/8f13910f-34bc-4018-ab6a-144bc742a444
-- title:
--   Lemma 9 — the gadget $K_n(u,v)$ confines a KT1 agent away from its gates for $\Omega(n^2)$ time
-- statement:
--   There are a constant $c>0$ and a threshold $N$ such that the following holds. Let $V$ be a finite set with $n=|V|\ge N$, let $u\ne v$ be two of its nodes, and let $K_n(u,v)$ be the complete graph on $V$ minus the edge $\{u,v\}$. Fix arbitrary distinct identifiers, an arbitrary port numbering of $K_n(u,v)$ and a starting node other than $u$ and $v$. Then for every deterministic KT1 algorithm $A$ there is an ∞-interval-connected schedule on the underlying graph $K_n(u,v)$ such that the agent running $A$ is at neither $u$ nor $v$ at any time
--   $$
--   t<c\,n^2 .
--   $$
--
--   Because the identifiers, ports and start are fixed before $A$, the algorithm may depend on them: the bound holds even if the agent knows the whole underlying graph with its port assignment in advance. The gadget is the confinement device of the lower bounds for the window size (Theorem 3) and for the KT1 exploration time (Theorem 5).
--
--   **Formalization Note** The paper's $\Omega(n^2)$ is an absolute constant $c$ chosen before $V$, the instance data and $A$; the proof's move count is $\sum_{k=2}^{n-3}(n-2-k)$ and "independent of the algorithm $A$". A run that halts or takes an invalid port stays where it is, which is at a trap.
--
--   Differences from the source:
--   - reading: "for any deterministic algorithm A and any sufficiently large n … requires Ω(n²) time to reach either u or v" (the order of quantifiers leaves open whether the constant and the threshold may depend on A) → ∃c>0, ∃N, and for n ≥ N the position at every time t < c·n² differs from u and from v; reason: the stronger, uniform reading, with absolute constants fixed before every instance and the algorithm; the proof says the bound "is independent of the algorithm A"
--   - encoding: "even if the agent knows the entire structure of the underlying graph, including the port assignments, a priori" → identifiers, ports and start universally quantified before the algorithm, schedule existential after it; reason: an algorithm chosen after the structure may encode it
-- source:
--   Yuichi Sudo, Naoki Kitamura, Masahiro Shibata, Junya Nakamura, Sébastien Tixeuil, Toshimitsu Masuzawa, Koichi Wada, STOC 2027 submission #1589 (October 2026), Lemma 9, p.13 (PDF p.14); proof pp.13–14 (PDF pp.14–15)

import Definitions.Def_IntervalExplore_KT1_Supplement_Model

set_option autoImplicit false

namespace IntervalExplore.KT1.Supplement

open IntervalExplore.KT1

/-- Lemma 9, p.13 (PDF p.14). Identifiers, ports and the start (any trap) are fixed before
the algorithm ("even if the agent knows … a priori"); the ∞-interval-connected schedule on
K_n(u,v) is chosen after it. Before time c·n² the agent is at neither gate. -/
theorem lemma_9 :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V],
      N ≤ Fintype.card V → ∀ u v : V, u ≠ v →
      ∀ (labels : V ↪ ℕ) (ports : Ports (gadget u v)) (start : V), start ≠ u → start ≠ v →
      ∀ A : Alg, ∃ D : DynamicGraph (gadget u v), InfIntervalConnected D ∧
        ∀ t : ℕ, (t : ℝ) < c * (Fintype.card V : ℝ) ^ 2 →
          (state ⟨gadget u v, D, labels, ports, start⟩ A t).position ≠ u ∧
          (state ⟨gadget u v, D, labels, ports, start⟩ A t).position ≠ v := by sorry

end IntervalExplore.KT1.Supplement
