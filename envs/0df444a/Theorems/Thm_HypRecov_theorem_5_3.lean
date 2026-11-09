-- Prove2me | Theorems.Thm_HypRecov_theorem_5_3
-- name    : HypRecov.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:38:54.821801+00:00
-- url     : https://prove2.me/theorems/61241703-a3cf-49e5-8193-0cb566665a51
-- title:
--   Theorem 5.3 — clique frontiers after completion
-- statement:
--   Throughout, $H$ is a simple $r$-uniform hypergraph on $V=\{0,\dots,n-1\}$ with $r\ge 2$, $k\ge 3$, $K=k-1$ and $M=2^{\lceil\log_2 k\rceil-1}$ (so $M\le K<2M$); $D\subseteq E(H)$ is a set of recovered edges and $J=H-D$ the residual hypergraph; $P_0$ is a safe base partition. A **small cut** is a set $S$ with $\mathrm{cut}_H(S)<k$.
--
--   1. **Caps and safety.** Consider the layered process (acceptances, rejections with block mergers, and arbitrary safe mergers) started from no deletions, the partition $P_0$ and $k$ empty layers. In every reachable state the current partition is safe and coarsens $P_0$, the deletion set $D\subseteq E(H)$ is exactly the union of the layers, there is one acceptance per deleted edge, there are at most $k(n-1)$ acceptances, and at most $n-1$ strict merges.
--   2. **Frontier at termination.** Let $D\subseteq E(H)$ and let $P$ be a safe coarsening of $P_0$ such that no edge qualifies for completion. For every small cut $S$ with $\delta_J(S)\ne\emptyset$ there is a shore $A$ whose crossing frontier $T=\{v\in A: v\text{ lies in an edge of }\delta_J(S)\}$ satisfies
--   $$T=Z\cap A,\qquad 1\le|T|<r,$$
--   and $T$ is a clique of $G(J)$.
--
--   Exhaustive completion therefore leaves on every surviving small cut a small clique frontier on one shore, which drives the separator search of §6.
--
--   Differences from the source:
--   - reading: the completion phase "interleaved with any genuine candidate processing and safe mergers" → the relation ProcStep: acceptance or rejection of any residual edge spanning current blocks, and any safe coarsening; caps for every reachable state; reason: the paper's phase is any such interleaving; completion steps are acceptances or rejections of qualifying edges (paper.md decision 9)
--   - generalization: "at a terminal state" of the phase → every D ⊆ E(H) and safe coarsening P of P₀ at which no edge qualifies; reason: terminal states are of this kind; the proof uses only these properties
--   - reading: "In particular T is a clique" → T is a clique of the two-section of J; reason: T ⊆ Z, and Lemma 5.1 makes Z a clique of the true two-section
--   - reading: cache records, edge labels and available complete lists (Proposition 4.1) → the true residual quantities avail, knownMembers, envelope, numPoints; reason: the arguments are deterministic on the cache success event (p.9), where every value read is the true one and labels are injective on T_K (paper.md decision 7)
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 5.3, p.11 (PDF p.12)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_twoSection
import Definitions.Def_HypRecov_Safe
import Definitions.Def_HypRecov_envelope
import Definitions.Def_HypRecov_heavyCore
import Definitions.Def_HypRecov_ProcStep

namespace HypRecov

/-- **Theorem 5.3 (Clique frontiers after completion).** Zhang, Chen, Shen, *Hypergraph Recovery from
Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem 5.3, p.11
(PDF p.12): "Starting with the fixed cache, repeatedly complete every tag appearing in an available
complete low-link list for which #{distinct available Cauchy points for e} ≥ 2 min{r − |P_e|,
|U_e| − r}. (∗) A completed edge spanning current blocks is inserted into the original k disjoint
greedy connectivity layers. If accepted, retain and genuinely delete it. If rejected by every layer,
safely merge its member blocks. Ignore completed edges internal to a current block. Restart after
each change. This phase, interleaved with any genuine candidate processing and safe mergers, has at
most k(n − 1) acceptances and n − 1 strict merges from empty layers. The deletion set consists exactly
of accepted edges. At a terminal state, for every original small cut S with nonempty residual
boundary F = δ_J(S), one of its shores A has crossing frontier T = {v ∈ A : v belongs to some edge of
F} = Z ∩ A, 1 ≤ |T| < r. In particular T is a clique. The conclusion holds simultaneously for all
original small-cut witnesses on the fixed-cache success event."

(i) Every state reachable from (no deletions, safe base partition `P₀`, empty layers) by acceptances,
rejections and safe mergers (`ProcStep`) has a safe current partition coarsening `P₀`, deletion set
`D ⊆ E(H)` equal to the union of the layers with one acceptance per deleted edge, at most `k(n − 1)`
acceptances and at most `n − 1` strict merges.
(ii) At every completion-terminal state, every small cut `S` with `δ_J(S) ≠ ∅` has a shore `A` whose
crossing frontier `T` equals `Z ∩ A`, has `1 ≤ |T| < r`, and is a clique of the two-section of `J`.

**Formalization Note.** The process is a relation (paper.md decision 9). Clause (ii) is stated for
every `D ⊆ E(H)` and every safe coarsening `P` of `P₀` at which no edge qualifies, which includes the
terminal states of the process. -/
theorem theorem_5_3 {n : ℕ} (E : Finset (Finset (Fin n))) (r k : ℕ) (hr : 2 ≤ r) (hk : 3 ≤ k)
    (hE : ∀ e ∈ E, e.card = r) (P₀ : Fin n → Fin n) (hP₀ : Safe E k P₀) :
    (∀ s : ProcState n k, Relation.ReflTransGen (ProcStep E k) (initState P₀) s →
      Safe E k s.P ∧ Coarsens P₀ s.P ∧ s.D ⊆ E ∧ s.D = Finset.univ.biUnion s.layers ∧
        s.acc = s.D.card ∧ s.acc ≤ k * (n - 1) ∧ s.mrg ≤ n - 1) ∧
    ∀ (D : Finset (Finset (Fin n))) (P : Fin n → Fin n), D ⊆ E → Coarsens P₀ P → Safe E k P →
      CompletionTerminal r (E \ D) P₀ P (Mpow k) →
      ∀ S : Finset (Fin n), cut E S < k → (bdry (E \ D) S).Nonempty →
        ∃ A : Finset (Fin n), (A = S ∨ A = Sᶜ) ∧
          frontier (E \ D) S A = heavyCore (E \ D) S (Mpow k) ∩ A ∧
          1 ≤ (frontier (E \ D) S A).card ∧ (frontier (E \ D) S A).card < r ∧
          (twoSection (E \ D)).IsClique (frontier (E \ D) S A : Set (Fin n)) := by sorry

end HypRecov
